module Time {
  // Returns the number of seconds since the Unix epoch
  method {:extern "TimeUtil.Time", "CurrentTime"} GetCurrent() returns (seconds: nat)
}
