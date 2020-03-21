module Time {
  // Returns the number of seconds since some fixed-as-long-as-this-program-is-running moment in the past
  method {:extern "TimeUtil.Time", "CurrentRelativeTime"} GetCurrent() returns (seconds: nat)
}
