package UTF8;

import dafny.DafnySequence;
import Wrappers_Compile.Result;

public class __default extends UTF8._ExternBase___default {

    public static Result<DafnySequence<? extends Byte>, DafnySequence<? extends Character>> Encode(DafnySequence<? extends Character> s) {
        return Result.create_Failure(null);
    }

    public static Result<DafnySequence<? extends Character>, DafnySequence<? extends Character>> Decode(DafnySequence<? extends Byte> b) {
        return Result.create_Failure(null);
    }
}
