package AESEncryption;

import dafny.DafnySequence;
import dafny.UByte;
import org.bouncycastle.crypto.InvalidCipherTextException;
import org.bouncycastle.crypto.engines.AESEngine;
import org.bouncycastle.crypto.modes.GCMBlockCipher;
import org.bouncycastle.crypto.params.AEADParameters;
import org.bouncycastle.crypto.params.KeyParameter;

//TODO This code has yet to be reviewed. See issue #36
public class AES_GCM {

    public static STL.Result<EncryptionOutput> AESEncrypt(EncryptionSuites.EncryptionSuite encAlg,
                                                  DafnySequence<UByte> iv,
                                                  DafnySequence<UByte> key,
                                                  DafnySequence<UByte> msg,
                                                  DafnySequence<UByte> aad) {
        try {
            GCMBlockCipher cipher = new GCMBlockCipher(new AESEngine());
            AEADParameters param = new AEADParameters(new KeyParameter(DafnySequence.toByteArrayUnsigned(key)), encAlg.tagLen.intValue() * 8, DafnySequence.toByteArrayUnsigned(iv), DafnySequence.toByteArrayUnsigned(aad));
            cipher.init(true, param);

            byte[] c = new byte[cipher.getOutputSize(msg.length())];
            int len = cipher.processBytes(DafnySequence.toByteArrayUnsigned(msg), 0, msg.length(), c, 0);
            cipher.doFinal(c, len); //Append authentication tag to `c`
            return new STL.Result_Success<EncryptionOutput>(__default.EncryptionOutputFromByteSeq(DafnySequence.fromBytesUnsigned(c), encAlg));
        }
        catch (InvalidCipherTextException e) {
            return new STL.Result_Failure<EncryptionOutput>(DafnySequence.asString("aes encrypt err"));
        }
    }

    public static STL.Result<DafnySequence<UByte>> AESDecrypt(EncryptionSuites.EncryptionSuite encAlg, DafnySequence<UByte> key, DafnySequence<UByte> cipherText, DafnySequence<UByte> authTag, DafnySequence<UByte> iv, DafnySequence<UByte> aad) {
        try {
            GCMBlockCipher cipher = new GCMBlockCipher(new AESEngine());
            AEADParameters param = new AEADParameters(new KeyParameter(DafnySequence.toByteArrayUnsigned(key)), encAlg.tagLen.intValue() * 8, DafnySequence.toByteArrayUnsigned(iv), DafnySequence.toByteArrayUnsigned(aad));
            cipher.init(false, param);
            DafnySequence<UByte> ctx = cipherText.concatenate(authTag);
            byte[] pt = new byte[cipher.getOutputSize(ctx.length())];
            int len = cipher.processBytes(DafnySequence.toByteArrayUnsigned(ctx), 0, ctx.length(), pt, 0);
            cipher.doFinal(pt, len); //Check message authentication tag
            return new STL.Result_Success<DafnySequence<UByte>>(DafnySequence.fromBytesUnsigned(pt));
        } catch (InvalidCipherTextException macEx) {
            return new STL.Result_Failure<DafnySequence<UByte>>(DafnySequence.asString(macEx.toString()));
        } catch (Exception e) {
            return new STL.Result_Failure<DafnySequence<UByte>>(DafnySequence.asString("aes decrypt err"));
        }
    }
}
