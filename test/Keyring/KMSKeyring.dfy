// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../Util/TestUtils.dfy"


module TestKMSKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KMSKeyringDef
  import KMSUtils
  method {:test} TestRegionParseValidInput() {
    var cmk := "arn:aws:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    expect KMSUtils.ValidFormatCMK(cmk);
    var res :- expect KMSKeyringDef.RegionFromKMSKeyARN(cmk);
    expect "us-west-1" == res;
  }
  method {:test} TestRegionParseValidInputWildPartition() {
    var cmk := "arn:xxx:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    expect KMSUtils.ValidFormatCMK(cmk);
    var res :- expect KMSKeyringDef.RegionFromKMSKeyARN(cmk);
    expect "us-west-1" == res;
  }
  method {:test} TestRegionParseValidInputNoPartition() {
    var cmk := "arn::kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    expect KMSUtils.ValidFormatCMK(cmk);
    var res :- expect KMSKeyringDef.RegionFromKMSKeyARN(cmk);
    expect "us-west-1" == res;
  }
  method {:test} TestRegionParseValidInputAliasArn() {
    var cmk := "arn:aws:kms:us-west-1:658956600833:alias/EncryptDecrypt";
    expect KMSUtils.ValidFormatCMK(cmk);
    var res :- expect KMSKeyringDef.RegionFromKMSKeyARN(cmk);
    expect "us-west-1" == res;
  }
  method {:test} TestRegionParseBadInputAlias() {
    var cmk := "alias/EncryptDecrypt";
    expect KMSUtils.ValidFormatCMK(cmk);
    var res := KMSKeyringDef.RegionFromKMSKeyARN(cmk);
    expect res.Failure? && res.error == "Malformed ARN";
  }
}
