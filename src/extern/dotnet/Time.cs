using System;
using System.Numerics;

namespace TimeUtil {

    public class Time {
        private static readonly DateTime UnixEpoch = new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc);

        public static BigInteger CurrentTime() {
            var timespan = DateTime.UtcNow - UnixEpoch;
            var seconds = (ulong)timespan.TotalSeconds;
            return new BigInteger(seconds);
        }
    }
}
