package AESEncryption;

import java.security.GeneralSecurityException;
import java.security.spec.AlgorithmParameterSpec;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.GCMParameterSpec;
import javax.crypto.spec.SecretKeySpec;

import Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput;
import Dafny.Aws.Cryptography.Primitives.Types.AES__GCM;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Random_Compile.ExternRandom;
import Wrappers_Compile.Result;

import dafny.Array;
import dafny.DafnySequence;

import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

public class AES_GCM {
    public static Result<AESEncryptOutput, Error> AESEncryptExtern(
            AES__GCM encAlg,
            DafnySequence<? extends Byte> iv,
            DafnySequence<? extends Byte> key,
            DafnySequence<? extends Byte> msg,
            DafnySequence<? extends Byte> aad
    ) {
        byte[] keyBytes = (byte[]) Array.unwrap(key.toArray());
        byte[] nonceBytes = (byte[]) Array.unwrap(iv.toArray());
        byte[] plaintextBytes = (byte[]) Array.unwrap(msg.toArray());
        final AlgorithmParameterSpec spec =
                new GCMParameterSpec(encAlg._tagLength * 8, nonceBytes, 0, nonceBytes.length);
        try {
            Cipher cipher_ = Cipher.getInstance("AES/GCM/NoPadding");
            SecretKey secretKey = new SecretKeySpec(keyBytes, "AES");
            cipher_.init(Cipher.ENCRYPT_MODE, secretKey, spec, ExternRandom.getSecureRandom());
            if (aad != null) {
                byte[] aadBytes = (byte[]) Array.unwrap(aad.toArray());
                cipher_.updateAAD(aadBytes);
            }
            byte[] cipherOutput = cipher_.doFinal(plaintextBytes);
            AESEncryptOutput aesEncryptOutput = __default.EncryptionOutputFromByteSeq(
                    DafnySequence.fromBytes(cipherOutput),
                    encAlg);
            return Result.create_Success(aesEncryptOutput);
        } catch ( GeneralSecurityException e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).build())
            );
        }
    }

    public static Result<DafnySequence<? extends Byte>, Error> AESDecryptExtern(
            AES__GCM encAlg,
            DafnySequence<? extends Byte> key,
            DafnySequence<? extends Byte> cipherTxt,
            DafnySequence<? extends Byte> authTag,
            DafnySequence<? extends Byte> iv,
            DafnySequence<? extends Byte> aad
    ) {
        byte[] keyBytes = (byte[]) Array.unwrap(key.toArray());
        byte[] nonceBytes = (byte[]) Array.unwrap(iv.toArray());
        byte[] ciphertextBytes = (byte[]) Array.unwrap(cipherTxt.toArray());
        byte[] tagBytes = (byte[]) Array.unwrap(authTag.toArray());
        byte[] ciphertextAndTag = new byte[ciphertextBytes.length + tagBytes.length];
        System.arraycopy(ciphertextBytes, 0, ciphertextAndTag, 0, ciphertextBytes.length);
        System.arraycopy(tagBytes, 0, ciphertextAndTag, ciphertextBytes.length, tagBytes.length);

        final AlgorithmParameterSpec spec =
                new GCMParameterSpec(encAlg._tagLength * 8, nonceBytes, 0, nonceBytes.length);
        try {
            Cipher cipher_ = Cipher.getInstance("AES/GCM/NoPadding");
            SecretKey secretKey = new SecretKeySpec(keyBytes, "AES");
            cipher_.init(Cipher.DECRYPT_MODE, secretKey, spec, ExternRandom.getSecureRandom());
            if (aad != null) {
                byte[] aadBytes = (byte[]) Array.unwrap(aad.toArray());
                cipher_.updateAAD(aadBytes);
            }
            byte[] cipherOutput = cipher_.doFinal(ciphertextAndTag);
            return Result.create_Success(DafnySequence.fromBytes(cipherOutput));
        } catch ( GeneralSecurityException e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).build())
            );
        }
    }
}
