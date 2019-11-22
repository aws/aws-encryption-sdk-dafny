package Time;

import java.math.BigInteger;

public class Timer {
    private long start;

    public Timer() {
        start = System.currentTimeMillis();
    }

    public BigInteger ElapsedMilliseconds() {
        return BigInteger.valueOf(System.currentTimeMillis() - start);
    }
}
