// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Modes;
using Org.BouncyCastle.Crypto.Parameters;

using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;


namespace AESEncryption {
    public partial class AES_GCM {

        public static _IResult<_IEncryptionOutput, icharseq> AESEncryptExtern(AESEncryption._IAES__GCM encAlg,
                                                      ibyteseq iv,
                                                      ibyteseq key,
                                                      ibyteseq msg,
                                                      ibyteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(
                    new KeyParameter(key.Elements),
                    (int)((AESEncryption.AES__GCM)encAlg).tagLength * 8,
                    iv.Elements,
                    aad.Elements);
                cipher.Init(true, param);

                byte[] c = new byte[cipher.GetOutputSize(msg.Elements.Length)];
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, c, 0);
                cipher.DoFinal(c, len); //Append authentication tag to `c`
                return Result<_IEncryptionOutput, icharseq>.create_Success(__default.EncryptionOutputFromByteSeq(byteseq.FromArray(c), encAlg));
            }
            catch {
                return DafnyFFI.CreateFailure<EncryptionOutput>("aes encrypt err");
            }
        }

        public static _IResult<ibyteseq, icharseq> AESDecryptExtern(AESEncryption._IAES__GCM encAlg, ibyteseq key, ibyteseq cipherText, ibyteseq authTag, ibyteseq iv, ibyteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(
                    new KeyParameter(key.Elements),
                    ((AESEncryption.AES__GCM)encAlg).tagLength * 8,
                    iv.Elements,
                    aad.Elements);
                cipher.Init(false, param);
                var ctx = byteseq.Concat(cipherText, authTag);
                var pt = new byte[cipher.GetOutputSize(ctx.Elements.Length)];
                var len = cipher.ProcessBytes(ctx.Elements, 0, ctx.Elements.Length, pt, 0);
                cipher.DoFinal(pt, len); //Check message authentication tag
                return Result<ibyteseq, icharseq>.create_Success(byteseq.FromArray(pt));
            } catch(InvalidCipherTextException macEx) {
                return DafnyFFI.CreateFailure<ibyteseq>(macEx.ToString());
            } catch {
                return DafnyFFI.CreateFailure<ibyteseq>("aes decrypt err");
            }
        }
    }
}
