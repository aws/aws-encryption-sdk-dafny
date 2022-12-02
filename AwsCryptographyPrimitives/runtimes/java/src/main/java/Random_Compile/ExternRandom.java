package Random_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.DafnySequence;

public class ExternRandom {
    public static class __default {

        public static Result<DafnySequence<? extends Byte>, Error> GenerateBytes(int i) {
            return Result.create_Success(null);
        }
    }
}
