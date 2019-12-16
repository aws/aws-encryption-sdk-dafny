include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../Util/TestUtils.dfy"


module TestKMSKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KMSKeyringDefs
  import KMSUtils
  method {:test} TestRegionParseValidInput() returns (r: Result<()>) {
    var cmk := "arn:aws:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    var _ :- Require(KMSUtils.ValidFormatCMK(cmk));
    var res :- KMSKeyringDefs.RegionFromKMSKeyARN(cmk);
    r := RequireEqual("us-west-1", res);
  }
  method {:test} TestRegionParseValidInputWildPartition() returns (r: Result<()>) {
    var cmk := "arn:xxx:kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    var _ :- Require(KMSUtils.ValidFormatCMK(cmk));
    var res :- KMSKeyringDefs.RegionFromKMSKeyARN(cmk);
    r := RequireEqual("us-west-1", res);
  }
  method {:test} TestRegionParseValidInputNoPartition() returns (r: Result<()>) {
    var cmk := "arn::kms:us-west-1:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    var _ :- Require(KMSUtils.ValidFormatCMK(cmk));
    var res :- KMSKeyringDefs.RegionFromKMSKeyARN(cmk);
    r := RequireEqual("us-west-1", res);
  }
  method {:test} TestRegionParseValidInputAliasArn() returns (r: Result<()>) {
    var cmk := "arn:aws:kms:us-west-1:658956600833:alias/EncryptDecrypt";
    var _ :- Require(KMSUtils.ValidFormatCMK(cmk));
    var res :- KMSKeyringDefs.RegionFromKMSKeyARN(cmk);
    r := RequireEqual("us-west-1", res);
  }
  method {:test} TestRegionParseBadInputAlias() returns (r: Result<()>) {
    var cmk := "alias/EncryptDecrypt";
    var _ :- Require(KMSUtils.ValidFormatCMK(cmk));
    var res := KMSKeyringDefs.RegionFromKMSKeyARN(cmk);
    r := Require(res.Failure? && res.error == "Malformed ARN");
  }
}
