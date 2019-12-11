// RUN: %dafny /out:Output/KMSKeyring.exe "./KMSKeyring.dfy" ../../src/extern/dotnet/KMS.cs ../../src/extern/dotnet/UTF8.cs "%kmslib" "%awslib" /compile:2
// RUN: cp %awslib %kmslib Output/
// RUN: %mono ./Output/KMSKeyring.exe > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"

module TestKMSKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KMSKeyring
  import KMSUtils
  method TestRegionParseValidInput() {
    var cmk := "arn:aws:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    if KMSUtils.ValidFormatCMK(cmk) {
      var res := KMSKeyring.RegionFromKMSKeyARN(cmk);
      if res.Success? && res.value == "us-west-1" {
        print "CORRECT\n";
      } else {
        print "NOT CORRECT\n";
      }
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInputWildPartition() {
    var cmk := "arn:xxx:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    if KMSUtils.ValidFormatCMK(cmk) {
      var res := KMSKeyring.RegionFromKMSKeyARN(cmk);
      if res.Success? && res.value == "us-west-1" {
        print "CORRECT\n";
      } else {
        print "NOT CORRECT\n";
      }
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInputNoPartition() {
    var cmk := "arn::kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    if KMSUtils.ValidFormatCMK(cmk) {
      var res := KMSKeyring.RegionFromKMSKeyARN(cmk);
      if res.Success? && res.value == "us-west-1" {
        print "CORRECT\n";
      } else {
        print "NOT CORRECT\n";
      }
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInputAliasArn() {
    var cmk := "arn:aws:kms:us-west-1:658956600833:alias/EncryptDecrypt";
    if KMSUtils.ValidFormatCMK(cmk) {
      var res := KMSKeyring.RegionFromKMSKeyARN(cmk);
      if res.Success? && res.value == "us-west-1" {
        print "CORRECT\n";
      } else {
        print "NOT CORRECT\n";
      }
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseBadInputAlias() {
    var cmk := "alias/EncryptDecrypt";
    if KMSUtils.ValidFormatCMK(cmk) {
      var res := KMSKeyring.RegionFromKMSKeyARN(cmk);
      if res.Failure? && res.error == "Malformed ARN" {
        print "CORRECT\n";
      } else {
        print "NOT CORRECT\n";
      }
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    TestRegionParseValidInput();
    TestRegionParseValidInputWildPartition();
    TestRegionParseValidInputNoPartition();
    TestRegionParseValidInputAliasArn();

    TestRegionParseBadInputAlias();
  }
}
