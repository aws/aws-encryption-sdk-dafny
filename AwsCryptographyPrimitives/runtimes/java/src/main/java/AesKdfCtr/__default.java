package AesKdfCtr;

import java.security.GeneralSecurityException;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.SecretKeySpec;
import javax.crypto.spec.IvParameterSpec;

import Wrappers_Compile.Result;

import dafny.Array;
import dafny.DafnySequence;

import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

public class __default {
    public static Wrappers_Compile.Result<dafny.DafnySequence<? extends Byte>, Dafny.Aws.Cryptography.Primitives.Types.Error>
    AesKdfCtrStream(dafny.DafnySequence<? extends Byte> iv, dafny.DafnySequence<? extends Byte> key, int length)
    {
        byte[] keyBytes = (byte[]) Array.unwrap(key.toArray());
        byte[] nonceBytes = (byte[]) Array.unwrap(iv.toArray());
        byte[] plaintext = new byte[length];
        try {
            Cipher cipher = Cipher.getInstance("AES/CTR/NoPadding");
            SecretKey secretKey = new SecretKeySpec(keyBytes, "AES");
            IvParameterSpec ivSpec = new IvParameterSpec(nonceBytes);
            cipher.init(Cipher.ENCRYPT_MODE, secretKey, ivSpec);
            byte[] ciphertext = cipher.doFinal(plaintext);
            return Result.create_Success(DafnySequence.fromBytes(ciphertext));
        } catch ( GeneralSecurityException e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).build())
            );
        }
    }
}
