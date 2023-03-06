// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/ConstantTime.dfy"

module ConstantTimeTest {
  import ConstantTime

  method {:test} ConstantTimeTest() {
    expect ConstantTime.Equals([],[]);
    expect ConstantTime.Equals([1],[1]);
    expect !ConstantTime.Equals([1],[2]);
    expect ConstantTime.Equals([1,2,3],[1,2,3]);
    expect !ConstantTime.Equals([2,2,3],[1,2,3]);
    expect !ConstantTime.Equals([1,2,3],[1,2,4]);
  }

}