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
import Wrappers_Compile.Result;

import dafny.Array;
import dafny.DafnySequence;

public class AES_GCM {
    public static Result<AESEncryptOutput, Error> AESEncryptExtern(
            AES__GCM encAlg,
            DafnySequence<? extends Byte> iv,
            DafnySequence<? extends Byte> key,
            DafnySequence<? extends Byte> msg,
            DafnySequence<? extends Byte> aad
    ) {
        return Result.create_Success(null);
    }

    public static Result<DafnySequence<? extends Byte>, Error> AESDecryptExtern(
            AES__GCM encAlg,
            DafnySequence<? extends Byte> key,
            DafnySequence<? extends Byte> cipherTxt,
            DafnySequence<? extends Byte> authTag,
            DafnySequence<? extends Byte> iv,
            DafnySequence<? extends Byte> aad
    ) {
        return Result.create_Success(null);
    }
}
