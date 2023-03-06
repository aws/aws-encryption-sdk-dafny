// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/FloatCompare.dfy"

module FloatCompareTest {
  import opened Wrappers
  import opened FloatCompare

  method TestCompareFloat(x : string, y : string, ret : CompareType)
    ensures CompareFloat(x, y) == ret
    ensures CompareFloat(y, x) == -ret
  {
    if CompareFloat(x, y) != ret {
      print "CompareFloat(", x, ", ", y, ") was ", CompareFloat(x, y), " but should have been ", ret, "\n";
    }
    if CompareFloat(y, x) != -ret {
      print "CompareFloat(", y, ", ", x, ") was ", CompareFloat(y, x), " but should have been ", -ret, "\n";
    }
    expect CompareFloat(x, y) == ret;
    expect CompareFloat(y, x) == -ret;
  }


  method {:test} FloatComparisonTest() {
    TestCompareFloat("1", "1", Equal);
    TestCompareFloat("2", "1", Greater);
    TestCompareFloat("1.1", "1.2", Less);
    TestCompareFloat("1.2", "1.2", Equal);
    TestCompareFloat("1.35", "1.357", Less);
    TestCompareFloat("1.35e2", "13.5e1", Equal);
    TestCompareFloat("1.351e2", "13.5e1", Greater);
    TestCompareFloat("1.35e-1", "13.5e-2", Equal);
    TestCompareFloat("1", "-2", Greater);
    TestCompareFloat("1.2e7", "2.3e2", Greater);
    TestCompareFloat("-1.2e7", "2.3e2", Less);
    TestCompareFloat("1.2e7", "-2.3e2", Greater);
    TestCompareFloat("-1.2e7", "-2.3e2", Less);
  }

  method {:test} ZeroTests() {
    TestCompareFloat("-0", "0", Less);
    TestCompareFloat("00", "0", Equal);
    TestCompareFloat("0.0", "0", Equal);
    TestCompareFloat("0", "000", Equal);
    TestCompareFloat("0", ".000", Equal);
    TestCompareFloat("0.0", "000.00000", Equal);

    TestCompareFloat("01", "1", Equal);
    TestCompareFloat("1", "001", Equal);
    TestCompareFloat("1.0", "001.00000", Equal);
  }

  // The results for non-numbers is undefined, but should be consistent
  // If DynamoDB has an opinion on this, we will agree with them
  method {:test} InvalidTests() {
    TestCompareFloat("a", "0", Greater);
    TestCompareFloat("a", "b", Less);
  }
}
