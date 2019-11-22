package Random;

import Utils.Util;
import dafny.DafnySequence;
import dafny.UByte;

import java.util.Random;

public class __default {
    public static DafnySequence<UByte> GenerateBytes(int i) {
        Random rng = new Random();
        byte[] z = new byte[i];
        rng.nextBytes(z);
        return Util.bytesToUByteSequence(z);
    }
}
