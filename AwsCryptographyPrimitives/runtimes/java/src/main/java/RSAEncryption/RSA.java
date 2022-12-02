package RSAEncryption;

import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Dafny.Aws.Cryptography.Primitives.Types.RSAPaddingMode;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import dafny.Tuple2;

public class RSA {
    private static int RSA_KEY_STRENGTH_MAX = 4096;
    private static String RSA_ERROR_MSG = String.format(
            "AWS Crypto will not generate an RSA Key with Strength greater than %s", RSA_KEY_STRENGTH_MAX);

    public static Tuple2<DafnySequence<? extends Byte>, DafnySequence<? extends Byte>> GenerateKeyPairExtern(int strength) {
        if (strength > RSA_KEY_STRENGTH_MAX) {
            throw new RuntimeException(RSA_ERROR_MSG);
        }
        return null;
    }

    public static Result<DafnySequence<? extends Byte>, Error> DecryptExtern(
            RSAPaddingMode dtor_padding,
            DafnySequence<? extends Byte> dtor_privateKey,
            DafnySequence<? extends Byte> dtor_cipherText
    ) {
        return null;
    }

    public static Result<DafnySequence<? extends Byte>, Error> EncryptExtern(
            RSAPaddingMode dtor_padding,
            DafnySequence<? extends Byte> dtor_publicKey,
            DafnySequence<? extends Byte> dtor_plaintext
    ) {
        return null;
    }
}
