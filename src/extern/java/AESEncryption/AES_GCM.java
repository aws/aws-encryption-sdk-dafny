package AESEncryption;

import dafny.DafnySequence;
import org.bouncycastle.crypto.InvalidCipherTextException;
import org.bouncycastle.crypto.engines.AESEngine;
import org.bouncycastle.crypto.modes.GCMBlockCipher;
import org.bouncycastle.crypto.params.AEADParameters;
import org.bouncycastle.crypto.params.KeyParameter;

//TODO This code has yet to be reviewed. See issue #36
public class AES_GCM {

    public static STL.Result<EncryptionOutput> AESEncrypt(EncryptionSuites.EncryptionSuite encAlg,
                                                  DafnySequence<Byte> iv,
                                                  DafnySequence<Byte> key,
                                                  DafnySequence<Byte> msg,
                                                  DafnySequence<Byte> aad) {
        try {
            GCMBlockCipher cipher = new GCMBlockCipher(new AESEngine());
            AEADParameters param = new AEADParameters(new KeyParameter(DafnySequence.toByteArray(key)), encAlg.tagLen * 8, DafnySequence.toByteArray(iv), DafnySequence.toByteArray(aad));
            cipher.init(true, param);

            byte[] c = new byte[cipher.getOutputSize(msg.length())];
            int len = cipher.processBytes(DafnySequence.toByteArray(msg), 0, msg.length(), c, 0);
            cipher.doFinal(c, len); //Append authentication tag to `c`
            return new STL.Result_Success<EncryptionOutput>(__default.EncryptionOutputFromByteSeq(DafnySequence.fromBytes(c), encAlg));
        }
        catch (InvalidCipherTextException e) {
            return new STL.Result_Failure<EncryptionOutput>(DafnySequence.asString("aes encrypt err"));
        }
    }

    public static STL.Result<DafnySequence<Byte>> AESDecrypt(EncryptionSuites.EncryptionSuite encAlg, DafnySequence<Byte> key, DafnySequence<Byte> cipherText, DafnySequence<Byte> authTag, DafnySequence<Byte> iv, DafnySequence<Byte> aad) {
        try {
            GCMBlockCipher cipher = new GCMBlockCipher(new AESEngine());
            AEADParameters param = new AEADParameters(new KeyParameter(DafnySequence.toByteArray(key)), encAlg.tagLen * 8, DafnySequence.toByteArray(iv), DafnySequence.toByteArray(aad));
            cipher.init(false, param);
            DafnySequence<Byte> ctx = cipherText.concatenate(authTag);
            byte[] pt = new byte[cipher.getOutputSize(ctx.length())];
            int len = cipher.processBytes(DafnySequence.toByteArray(ctx), 0, ctx.length(), pt, 0);
            cipher.doFinal(pt, len); //Check message authentication tag
            return new STL.Result_Success<DafnySequence<Byte>>(DafnySequence.fromBytes(pt));
        } catch (InvalidCipherTextException macEx) {
            return new STL.Result_Failure<DafnySequence<Byte>>(DafnySequence.asString(macEx.toString()));
        } catch (Exception e) {
            return new STL.Result_Failure<DafnySequence<Byte>>(DafnySequence.asString("aes decrypt err"));
        }
    }
}
