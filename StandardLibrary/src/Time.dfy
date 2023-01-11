// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"
include "./UInt.dfy"

module {:extern "Time"} Time {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // Returns the number of seconds since some fixed-as-long-as-this-program-is-running moment in the past
  method {:extern "CurrentRelativeTime"} GetCurrent() returns (res: uint64)
}
