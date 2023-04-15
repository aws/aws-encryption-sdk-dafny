// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"
include "./UInt.dfy"

module {:extern "Time"} Time {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  // Returns the number of seconds since some fixed-as-long-as-this-program-is-running moment in the past
  // Time is represented as signed over unsigned because java does not do unsigned 
  // values - net can do both so we are able to change the representation to signed.
  method {:extern "CurrentRelativeTime"} GetCurrent() returns (res: int64)
    // We are able to make this claim because it does not make sense for time to 
    // be negative.
    ensures res >= 0
  
  // Returns a timestamp for the current time in ISO8601 format in UTC
  // to microsecond precision (e.g. “YYYY-MM-DDTHH:mm:ss.ssssssZ“)
  function method {:extern "GetCurrentTimeStamp"} GetCurrentTimeStamp(): (res: Result<string, string>)
}
