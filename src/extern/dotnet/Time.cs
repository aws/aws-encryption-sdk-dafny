using System;
using System.Diagnostics;
using System.Numerics;

namespace Time {
  //public partial class __default {
  //  public static BigInteger CurrentTimeMillis() {
  //    return DateTime.Now.Ticks / TimeSpan.TicksPerMillisecond;
  //  }
  //}

  public class Timer {
    private readonly Stopwatch stopwatch = new Stopwatch();

    public Timer() {
      stopwatch.Start();
    }

    public BigInteger ElapsedMilliseconds() {
      return stopwatch.ElapsedMilliseconds;
    }
  }
}