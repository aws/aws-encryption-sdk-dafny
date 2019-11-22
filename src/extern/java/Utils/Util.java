package Utils;

import dafny.DafnySequence;
import dafny.UByte;

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

    public static UByte[] bytesToUBytes(byte[] bytes) {
        int len = bytes.length;
        UByte[] ans = new UByte[len];
        for (int i = 0; i < len; i++) {
            ans[i] = new UByte(bytes[i]);
        }
        return ans;
    }

    public static byte[] uBytesToBytes(UByte[] uBytes) {
        int len = uBytes.length;
        byte[] ans = new byte[len];
        for (int i = 0; i < len; i++) {
            ans[i] = uBytes[i].byteValue();
        }
        return ans;
    }

    public static DafnySequence<UByte> bytesToUByteSequence(byte[] bytes) {
        return DafnySequence.fromArray(bytesToUBytes(bytes));
    }

    public static byte[] uByteSequenceToBytes(DafnySequence<UByte> seq) {
        int len = seq.length();
        byte[] ans = new byte[len];
        int i = 0;
        for (UByte b : seq) {
            ans[i++] = b.byteValue();
        }
        return ans;
    }

    public static DafnySequence<UByte> stringToUByteSequence(String string) {
        return bytesToUByteSequence(string.getBytes(StandardCharsets.UTF_8));
    }

    public static String uByteSequenceToString(DafnySequence<UByte> uBytes) {
        return new String(uByteSequenceToBytes(uBytes), StandardCharsets.UTF_8);
    }
}
