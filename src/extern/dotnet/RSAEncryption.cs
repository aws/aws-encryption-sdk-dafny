using System;
using System.Text;
using System.IO;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;

using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;

namespace RSAEncryption {

    public class RSAUnsupportedPaddingSchemeException : Exception
    {
        public RSAUnsupportedPaddingSchemeException(string paddingScheme)
            : base(String.Format("Invalid RSA Padding Scheme: {0}", paddingScheme))
        {
        }
    }

    public partial class RSA {

        // The following represent common, recommended RSA constants
        const int RSA_PUBLIC_EXPONENT = (65537);
        const int RSA_CERTAINTY = 256;

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
        private static IAsymmetricBlockCipher GetEngineForPadding(PaddingMode padding) {
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
                throw new RSAUnsupportedPaddingSchemeException(padding.ToString());
            }
        }

        // GetPublicKeyFromByteSeq represents a helper method that takes in a byteseq representing a public
        // key and returns the AsymmetricKeyParameter for that public key, encoded using UTF-8
        private static AsymmetricKeyParameter GetPublicKeyFromByteSeq(byteseq key) {
            AsymmetricKeyParameter keyParam;
            using (var stringReader = new StringReader(Encoding.UTF8.GetString(key.Elements))) {
                return (AsymmetricKeyParameter) new PemReader(stringReader).ReadObject();
            }
        }

        public static void GenerateKeyPairExtern(int strength, PaddingMode padding, out byteseq publicKey, out byteseq privateKey) {
            RsaKeyPairGenerator keygen = new RsaKeyPairGenerator();
            SecureRandom secureRandom = new SecureRandom();
            keygen.Init(new RsaKeyGenerationParameters(
                BigInteger.ValueOf(RSA_PUBLIC_EXPONENT), secureRandom, strength, RSA_CERTAINTY));
            AsymmetricCipherKeyPair keygenPair = keygen.GenerateKeyPair();
            byte[] publicKeyBytes;
            byte[] privateKeyBytes;
            GetPemBytes(keygenPair, out publicKeyBytes, out privateKeyBytes);
            publicKey = byteseq.FromArray(publicKeyBytes);
            privateKey = byteseq.FromArray(privateKeyBytes);
        }

        public static STL.Result<byteseq> EncryptExtern(PaddingMode padding, byteseq publicKey, byteseq plaintextMessage) {
            try {
                IAsymmetricBlockCipher engine = GetEngineForPadding(padding);
                AsymmetricKeyParameter publicKeyParam = GetPublicKeyFromByteSeq(publicKey);
                engine.Init(true, publicKeyParam);
                return new STL.Result_Success<byteseq>(byteseq.FromArray(
                    engine.ProcessBlock(plaintextMessage.Elements, 0, plaintextMessage.Elements.Length)));
            }
            catch {
                return new STL.Result_Failure<byteseq>(charseq.FromArray("rsa encrypt error".ToCharArray()));
            }
        }

        public static STL.Result<byteseq> DecryptExtern(PaddingMode padding, byteseq privateKey, byteseq cipherText) {
            try {
                IAsymmetricBlockCipher engine = GetEngineForPadding(padding);
                AsymmetricCipherKeyPair keyPair;
                using ( var stringReader = new StringReader(Encoding.UTF8.GetString(privateKey.Elements))) {
                    // This needs to be read as an AsymmetricCipherKeyPair and cannot be read directly as a
                    // AsymmetricKeyParameter like the public key can
                    keyPair = (AsymmetricCipherKeyPair) new PemReader(stringReader).ReadObject();
                }
                engine.Init(false, keyPair.Private);
                return new STL.Result_Success<byteseq>(byteseq.FromArray(
                    engine.ProcessBlock(cipherText.Elements, 0, cipherText.Elements.Length)));
            }
            catch {
                return new STL.Result_Failure<byteseq>(charseq.FromArray("rsa decrypt error".ToCharArray()));
            }
        }
    }
}
