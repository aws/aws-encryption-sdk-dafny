package Random;

import dafny.DafnySequence;

import java.util.Random;

public class __default {
    public static DafnySequence<Byte> GenerateBytes(int i) {
        Random rng = new Random();
        byte[] z = new byte[i];
        rng.nextBytes(z);
        return DafnySequence.fromBytes(z);
    }
}
