// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Linq;
using System.Security.Cryptography;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Security;
using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;


namespace AESEncryption {
    public partial class AES_GCM {
        public static _IResult<_IEncryptionOutput, icharseq> AESEncryptExtern(
            AESEncryption._IAES__GCM encAlg,
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

            var ciphertextNoTag = new byte[plaintextBytes.Length];
            var tag = new byte[encAlg.dtor_tagLength];

            try
            {
                // System.Security.Cryptography.AesGcm is absent in .NET Framework
#if NETFRAMEWORK
                var param = new AeadParameters(
                    new KeyParameter(keyBytes),
                    encAlg.dtor_tagLength * 8,
                    iv.Elements,
                    aad.Elements);
                var cipher = CipherUtilities.GetCipher("AES/GCM/NoPadding");
                cipher.Init(true, param);

                var ciphertext = new byte[cipher.GetOutputSize(msg.Elements.Length)];
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, ciphertext, 0);
                cipher.DoFinal(ciphertext, len);  // Append authentication tag
#else
                var cipher = new AesGcm(keyBytes);
                cipher.Encrypt(nonceBytes, plaintextBytes, ciphertextNoTag, tag, aadBytes);
                var ciphertext = ciphertextNoTag.Concat(tag).ToArray();
#endif
                return Result<_IEncryptionOutput, icharseq>.create_Success(
                    __default.EncryptionOutputFromByteSeq(byteseq.FromArray(ciphertext), encAlg));
            }
            catch (Exception ex)
            {
                var message = string.IsNullOrEmpty(ex.Message) ? "" : $": {ex.Message}";
                return DafnyFFI.CreateFailure<EncryptionOutput>("AES encrypt error" + message);
            }
        }

        public static _IResult<ibyteseq, icharseq> AESDecryptExtern(
            AESEncryption._IAES__GCM encAlg,
            ibyteseq key,
            ibyteseq cipherText,
            ibyteseq authTag,
            ibyteseq iv,
            ibyteseq aad
        ) {
            try {
                var param = new AeadParameters(
                    new KeyParameter(key.Elements),
                    ((AESEncryption.AES__GCM)encAlg).tagLength * 8,
                    iv.Elements,
                    aad.Elements);
                var cipher = CipherUtilities.GetCipher("AES/GCM/NoPadding");
                cipher.Init(false, param);
                var ctx = byteseq.Concat(cipherText, authTag);
                var pt = new byte[cipher.GetOutputSize(ctx.Elements.Length)];
                cipher.DoFinal(ctx.Elements, pt, 0);
                return Result<ibyteseq, icharseq>.create_Success(byteseq.FromArray(pt));
            } catch(InvalidCipherTextException macEx) {
                return DafnyFFI.CreateFailure<ibyteseq>(macEx.ToString());
            } catch (Exception e) {
                return DafnyFFI.CreateFailure<ibyteseq>("aes decrypt error");
            }
        }
    }
}
