// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Linq;
using System.Security.Cryptography;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Security;
using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;
using _IAES__GCM = software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM;
using _IAESEncryptOutput = software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput;
using _IError = software.amazon.cryptography.primitives.internaldafny.types._IError;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;


namespace AESEncryption {
    public partial class AES_GCM {
        public static _IResult<_IAESEncryptOutput, _IError> AESEncryptExtern(
            _IAES__GCM encAlg,
            ibyteseq iv,
            ibyteseq key,
            ibyteseq msg,
            ibyteseq aad
        )
        {
            var keyBytes = key.Elements;
            var nonceBytes = iv.Elements;
            var plaintextBytes = msg.Elements;
            var aadBytes = aad.Elements;
            var ciphertext = new byte[plaintextBytes.Length + encAlg.dtor_tagLength];

            try
            {
                // System.Security.Cryptography.AesGcm is absent in .NET Framework
#if NETFRAMEWORK
                var param = new AeadParameters(
                    new KeyParameter(keyBytes),
                    encAlg.dtor_tagLength * 8,
                    nonceBytes,
                    aadBytes);
                var cipher = CipherUtilities.GetCipher("AES/GCM/NoPadding");
                cipher.Init(true, param);
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, ciphertext, 0);
                cipher.DoFinal(ciphertext, len);  // Append authentication tag
#else
                var aesCiphertext = new Span<byte>(ciphertext, 0, plaintextBytes.Length);
                var tag = new Span<byte>(ciphertext, plaintextBytes.Length, encAlg.dtor_tagLength);
                var cipher = new AesGcm(keyBytes);
                cipher.Encrypt(nonceBytes, plaintextBytes, aesCiphertext, tag, aadBytes);
#endif
                return Result<_IAESEncryptOutput, _IError>.create_Success(
                    __default.EncryptionOutputFromByteSeq(byteseq.FromArray(ciphertext), encAlg));
            }
            catch (Exception ex)
            {
                return Wrappers_Compile.Result<_IAESEncryptOutput, _IError>
                    .create_Failure(new Error_Opaque(ex));
            }
        }

        public static _IResult<ibyteseq, _IError> AESDecryptExtern(
            _IAES__GCM encAlg,
            ibyteseq key,
            ibyteseq cipherText,
            ibyteseq authTag,
            ibyteseq iv,
            ibyteseq aad
        ) {
            var keyBytes = key.Elements;
            var nonceBytes = iv.Elements;
            var ciphertextBytes = cipherText.Elements;
            var aadBytes = aad.Elements;
            var tagBytes = authTag.Elements;

            var plaintext = new byte[ciphertextBytes.Length];

            try {
#if NETFRAMEWORK
                var ciphertextAndTag = ciphertextBytes.Concat(tagBytes).ToArray();
                var param = new AeadParameters(
                    new KeyParameter(keyBytes),
                    encAlg.dtor_tagLength * 8,
                    nonceBytes,
                    aadBytes);
                var cipher = CipherUtilities.GetCipher("AES/GCM/NoPadding");
                cipher.Init(false, param);
                cipher.DoFinal(ciphertextAndTag, plaintext, 0);
#else
                var cipher = new AesGcm(keyBytes);
                cipher.Decrypt(nonceBytes, ciphertextBytes, tagBytes, plaintext, aadBytes);
#endif
                return Result<ibyteseq, _IError>
                    .create_Success(byteseq.FromArray(plaintext));
            }
            catch (Exception ex)
            {
                return Wrappers_Compile.Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(ex));
            }
        }
    }
}
