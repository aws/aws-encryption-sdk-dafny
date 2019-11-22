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
  method TestRegionParseValidInput0() {
    var res := KMSKeyring.RegionFromKMSKeyARN("arn:aws:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    if res.Success? && res.value == "us-west-1" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInput1() {
    var res := KMSKeyring.RegionFromKMSKeyARN("arn:xxx:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    if res.Success? && res.value == "us-west-1" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInput2() {
    var res := KMSKeyring.RegionFromKMSKeyARN("arn::kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    if res.Success? && res.value == "us-west-1" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseValidInput3() {
    var res := KMSKeyring.RegionFromKMSKeyARN("arn:aws:kms:us-west-1:658956600833:alias/EncryptDecrypt");
    if res.Success? && res.value == "us-west-1" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseBadInput0() {
    var res := KMSKeyring.RegionFromKMSKeyARN("arn:aws:s3:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    if res.Failure? && res.error == "Malformed ARN" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
  method TestRegionParseBadInput1() {
    var res := KMSKeyring.RegionFromKMSKeyARN("alias/EncryptDecrypt");
    if res.Failure? && res.error == "Malformed ARN" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    TestRegionParseValidInput0();
    TestRegionParseValidInput1();
    TestRegionParseValidInput2();
    TestRegionParseValidInput3();

    TestRegionParseBadInput0();
    TestRegionParseBadInput1();
  }
}
