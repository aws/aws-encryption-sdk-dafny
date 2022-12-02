package Signature;

import Dafny.Aws.Cryptography.Primitives.Types.ECDSASignatureAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.DafnySequence;

public class ECDSA {
    public static Result<SignatureKeyPair, Error> ExternKeyGen(
            ECDSASignatureAlgorithm dtor_signatureAlgorithm
    ) {
        return Result.create_Success(SignatureKeyPair.Default());
    }

    public static Result<DafnySequence<? extends Byte>, Error> Sign(
            ECDSASignatureAlgorithm dtor_signatureAlgorithm,
            DafnySequence<? extends Byte> dtor_signingKey,
            DafnySequence<? extends Byte> dtor_message
    ) {
        return Result.create_Success(null);
    }

    public static Result<Boolean, Error> Verify(
            ECDSASignatureAlgorithm dtor_signatureAlgorithm,
            DafnySequence<? extends Byte> dtor_verificationKey,
            DafnySequence<? extends Byte> dtor_message,
            DafnySequence<? extends Byte> dtor_signature
    ) {
        return Result.create_Success(Boolean.TRUE);
    }
}
