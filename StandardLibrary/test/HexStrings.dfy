// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/HexStrings.dfy"

module TestHexStrings {
  import opened HexStrings
  
  method {:test} BasicTests() {
    expect ToHexString([1,2,255]) == "0102ff";
    expect FromHexString("0102ff") == [1,2,255];
  }
}
