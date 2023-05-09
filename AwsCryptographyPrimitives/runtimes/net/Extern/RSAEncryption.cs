// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Diagnostics;
using System.Text;
using System.IO;
using software.amazon.cryptography.primitives.internaldafny.types;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;

using Wrappers_Compile;
using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;

using _IError = software.amazon.cryptography.primitives.internaldafny.types._IError;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;

namespace RSAEncryption {

    public partial class RSA {

        // The following represent common, recommended RSA constants
        const int RSA_PUBLIC_EXPONENT = (65537);
        const int RSA_CERTAINTY = 256;

        public static byte[] ParsePEMString(string pem) {
            AsymmetricKeyParameter key = (AsymmetricKeyParameter) new PemReader(new StringReader(pem)).ReadObject();
            using (StringWriter stringWriter = new StringWriter()) {
                PemWriter pemWriter = new PemWriter(stringWriter);
                pemWriter.WriteObject(key);
                return Encoding.UTF8.GetBytes(stringWriter.ToString());
            }
        }

        // GetPemBytes represents a helper method that takes an AsymmetricCipherKeyPair and returns the corresponding
        // private and public keys as UTF-8 byte arrays
        private static void GetPemBytes(AsymmetricCipherKeyPair keyPair, out byte[] publicKeyBytes, out byte[] privateKeyBytes) {
            using (var stringWriter = new StringWriter()) {
                var pemWriter = new PemWriter(stringWriter);
                pemWriter.WriteObject(keyPair.Public);
                publicKeyBytes = Encoding.UTF8.GetBytes(stringWriter.ToString());
            }

            using (var stringWriter = new StringWriter()) {
                var pemWriter = new PemWriter(stringWriter);
                pemWriter.WriteObject(keyPair.Private);
                privateKeyBytes = Encoding.UTF8.GetBytes(stringWriter.ToString());
            }
        }

        // GetEngineForPadding represents a helper method that takes in an PaddingMode and returns a
        // IAsymmetricBlockCipher for the RsaBlindedEngine that uses the appropriate digest or throws a
        // RSAUnsupportedPaddingSchemeException if no valid padding exists
        private static IAsymmetricBlockCipher GetEngineForPadding(_IRSAPaddingMode padding) {
            if (padding.is_PKCS1) {
                return new Pkcs1Encoding(new RsaBlindedEngine());
            } else if (padding.is_OAEP__SHA1) {
                return new OaepEncoding(new RsaBlindedEngine(), new Sha1Digest());
            } else if (padding.is_OAEP__SHA256) {
                return new OaepEncoding(new RsaBlindedEngine(), new Sha256Digest());
            } else if (padding.is_OAEP__SHA384) {
                return new OaepEncoding(new RsaBlindedEngine(), new Sha384Digest());
            } else if (padding.is_OAEP__SHA512) {
                return new OaepEncoding(new RsaBlindedEngine(), new Sha512Digest());
            } else {
                throw new System.Exception(String.Format("Invalid RSA Padding Scheme: {0}", padding));
            }
        }

        // GetPublicKeyFromByteSeq represents a helper method that takes in a byteseq representing a public
        // key and returns the AsymmetricKeyParameter for that public key, encoded using UTF-8
        private static AsymmetricKeyParameter GetPublicKeyFromByteSeq(ibyteseq key) {
            AsymmetricKeyParameter keyParam;
            using (var stringReader = new StringReader(Encoding.UTF8.GetString(key.CloneAsArray()))) {
                return (AsymmetricKeyParameter) new PemReader(stringReader).ReadObject();
            }
        }

        /// <summary>
        /// Reads the given PEM-encoded RSA private key, and returns the corresponding PEM-encoded public key.
        /// </summary>
        public static byte[] GetPublicKeyFromPrivateKeyPemString(string pem)
        {
            RsaPrivateCrtKeyParameters privateKeyParams;
            using (var stringReader = new StringReader(pem))
            {
                var pemObject = new PemReader(stringReader).ReadObject();
                try
                {
                    privateKeyParams = (RsaPrivateCrtKeyParameters)pemObject;
                }
                catch (InvalidCastException ex)
                {
                    throw new ArgumentException("Expected RSA private key", nameof(pem), ex);
                }
            }
            Debug.Assert(privateKeyParams != null);

            RsaKeyParameters publicKeyParams =
                new RsaKeyParameters(false, privateKeyParams.Modulus, privateKeyParams.PublicExponent);

            using (var stringWriter = new StringWriter())
            {
                new PemWriter(stringWriter).WriteObject(publicKeyParams);
                return Encoding.UTF8.GetBytes(stringWriter.ToString());
            }
        }

        public static void GenerateKeyPairBytes(int lengthBits, out byte[] publicKeyBytes, out byte[] privateKeyBytes) {
            RsaKeyPairGenerator keygen = new RsaKeyPairGenerator();
            SecureRandom secureRandom = new SecureRandom();
            keygen.Init(new RsaKeyGenerationParameters(
                BigInteger.ValueOf(RSA_PUBLIC_EXPONENT), secureRandom, lengthBits, RSA_CERTAINTY));
            AsymmetricCipherKeyPair keygenPair = keygen.GenerateKeyPair();
            GetPemBytes(keygenPair, out publicKeyBytes, out privateKeyBytes);
        }

        public static void GenerateKeyPairExtern(int lengthBits, out ibyteseq publicKey, out ibyteseq privateKey) {
            byte[] publicKeyBytes;
            byte[] privateKeyBytes;
            GenerateKeyPairBytes(lengthBits, out publicKeyBytes, out privateKeyBytes);
            publicKey = byteseq.FromArray(publicKeyBytes);
            privateKey = byteseq.FromArray(privateKeyBytes);
        }

        public static _IResult<uint, _IError> GetRSAKeyModulusLengthExtern(ibyteseq publicKey) {
            try {
                AsymmetricKeyParameter publicKeyParam = GetPublicKeyFromByteSeq(publicKey);
                RsaKeyParameters key = (RsaKeyParameters) publicKeyParam;
                return Result<uint, _IError>.create_Success((uint)key.Modulus.BitLength);
            }
            catch (Exception encryptEx) {
                return Result<uint, _IError>
                    .create_Failure(new Error_Opaque(encryptEx));
            }
        }

        public static _IResult<ibyteseq, _IError> EncryptExtern(_IRSAPaddingMode padding, ibyteseq publicKey, ibyteseq plaintextMessage) {
            try {
                IAsymmetricBlockCipher engine = GetEngineForPadding(padding);
                AsymmetricKeyParameter publicKeyParam = GetPublicKeyFromByteSeq(publicKey);
                engine.Init(true, publicKeyParam);
                var plaintextMessageBytes = plaintextMessage.CloneAsArray();
                return Result<ibyteseq, _IError>.create_Success(byteseq.FromArray(
                    engine.ProcessBlock(plaintextMessageBytes, 0, plaintextMessageBytes.Length)));
            }
            catch (Exception encryptEx) {
                return Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(encryptEx));
            }
        }

        public static _IResult<ibyteseq, _IError> DecryptExtern(_IRSAPaddingMode padding, ibyteseq privateKey, ibyteseq cipherText) {
            try {
                IAsymmetricBlockCipher engine = GetEngineForPadding(padding);
                AsymmetricKeyParameter privateKeyParameters = GetPrivateKeyFromByteSeq(privateKey.CloneAsArray());
                engine.Init(false, privateKeyParameters);
                var cipherTextBytes = cipherText.CloneAsArray();
                return Result<ibyteseq, _IError>.create_Success(byteseq.FromArray(
                    engine.ProcessBlock(cipherTextBytes, 0, cipherTextBytes.Length)));
            }
            catch (Exception decryptEx) {
                return Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(decryptEx));
            }
        }
        
        /// <summary>
        /// Reads the given PEM-encoded private key, and returns the corresponding AsymmetricKeyParameter.
        /// This is complicated because a PEM MAY contain both keys as a pair
        /// or MAY only contain the private key.
        /// </summary>
        public static AsymmetricKeyParameter GetPrivateKeyFromByteSeq(
            byte[] pemDataBlob
        ) {
            using ( var stringReader = new StringReader(Encoding.UTF8.GetString(pemDataBlob))) {

                switch (new PemReader(stringReader).ReadObject())
                {
                    // These casts are for correctness.
                    // This is to return RSA parameters,
                    // and these two types both extend from AsymmetricKeyParameter.
                    // But also other things do as well (elliptic curves),
                    // these checks are to make sure that we only get RSA keys back.
                    case AsymmetricCipherKeyPair keypair:
                        var keyParams = (RsaPrivateCrtKeyParameters)keypair.Private;
                        return keyParams;
                    case RsaKeyParameters keyParameter:
                        return keyParameter;
                    default:
                        throw new ArgumentException("PEM does not contain an RSA private key.");
                }
            }
        }
    }
}
