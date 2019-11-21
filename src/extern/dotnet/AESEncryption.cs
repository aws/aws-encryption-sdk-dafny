using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Modes;
using Org.BouncyCastle.Crypto.Parameters;

using byteseq = Dafny.Sequence<byte>;
using bytearrayseq = Dafny.ArraySequence<byte>;


namespace AESEncryption {
    //TODO This code has yet to be reviewed. See issue #36
    public partial class AES_GCM {

        public static STL.Result<EncryptionOutput> AESEncrypt(EncryptionSuites.EncryptionSuite encAlg,
                                                      byteseq iv,
                                                      byteseq key,
                                                      byteseq msg,
                                                      byteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(new KeyParameter(key.Elements), (int)encAlg.tagLen * 8, iv.Elements, aad.Elements);
                cipher.Init(true, param);

                byte[] c = new byte[cipher.GetOutputSize(msg.Elements.Length)];
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, c, 0);
                cipher.DoFinal(c, len); //Append authentication tag to `c`
                return new STL.Result_Success<EncryptionOutput>(__default.EncryptionOutputFromByteSeq(byteseq.FromElements(c), encAlg));
            }
            catch {
                return new STL.Result_Failure<EncryptionOutput>(new Dafny.ArraySequence<char>("aes encrypt err".ToCharArray()));
            }
        }

        public static STL.Result<byteseq> AESDecrypt(EncryptionSuites.EncryptionSuite encAlg, byteseq key, byteseq cipherText, byteseq authTag, byteseq iv, byteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(new KeyParameter(key.Elements), encAlg.tagLen * 8, iv.Elements, aad.Elements);
                cipher.Init(false, param);
                var ctx = cipherText.Concat(authTag);
                var pt = new byte[cipher.GetOutputSize(ctx.Elements.Length)];
                var len = cipher.ProcessBytes(ctx.Elements, 0, ctx.Elements.Length, pt, 0);
                cipher.DoFinal(pt, len); //Check message authentication tag
                return new STL.Result_Success<byteseq>(new bytearrayseq(pt));
            } catch(InvalidCipherTextException macEx) {
                return new STL.Result_Failure<byteseq>(new Dafny.ArraySequence<char>(macEx.ToString().ToCharArray()));
            } catch {
                return new STL.Result_Failure<byteseq>(new Dafny.ArraySequence<char>("aes decrypt err".ToCharArray()));
            }
        }
    }
}
