// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/Time.dfy"

module TestTime {
  import Time
  
  method {:test} TestNonDecreasing() {
    var t1 := Time.GetCurrent();
    var t2 := Time.GetCurrent();
    expect t2 >= t1;
  }

  method {:test} TestPositiveValues() {
    var t1 := Time.GetCurrent();
    var t2 := Time.GetCurrent();
    expect t2 - t1 >= 0;
  }
}
