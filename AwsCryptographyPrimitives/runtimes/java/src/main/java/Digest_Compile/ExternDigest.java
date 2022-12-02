package Digest_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.DafnySequence;

public class ExternDigest {
    public static class __default {

        public static Result<DafnySequence<? extends Byte>, Error> Digest(
                DigestAlgorithm digestAlgorithm,
                DafnySequence<? extends Byte> message
        ) {
            return Result.create_Success(null);
        }
    }
}
