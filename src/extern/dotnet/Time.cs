using System;
using System.Numerics;

namespace TimeUtil {
    public class Time {
        public static BigInteger CurrentRelativeTime() {
            var timespan = DateTime.Now - DateTime.MinValue;
            var seconds = (ulong)timespan.TotalSeconds;
            return new BigInteger(seconds);
        }
    }
}
