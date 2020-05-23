package Utils;

import dafny.DafnySequence;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;

public class Util {
    private Util() { }

    public static int bigIntegerToInt(BigInteger x) {
        try {
            return x.intValueExact();
        } catch(ArithmeticException e) {
            // TODO: error handling
            System.out.println(e.toString());
            throw e;
        }
    }

    public static String byteSequenceToString(DafnySequence<Byte> bytes) {
        return new String(DafnySequence.toByteArray(bytes), StandardCharsets.UTF_8);
    }
}
