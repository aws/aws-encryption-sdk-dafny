include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"
include "../Util/TestUtils.dfy"

module IntegTestKMS {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened TestUtils
  import CMMDefs
  import DefaultCMMDef
  import KMSUtils
  import KMSKeyringDef
  import Materials
  import Client = ESDKClient
  import EncryptionContext
  import UTF8
  import Base64

  const CURRENT_REGION := "us-west-2";

  // To avoid a "Public method '...' should be marked as a Theory" warning from xUnit, these helper methods are
  // declared in their own module.
  module Helpers {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened TestUtils
    import CMMDefs
    import DefaultCMMDef
    import KMSUtils
    import KMSKeyringDef
    import Materials
    import Client = ESDKClient
    import EncryptionContext
    import UTF8
    import Base64

    method EncryptDecryptTest(cmm: CMMDefs.CMM, shouldFailGetClient: bool)
      requires cmm.Valid()
      modifies cmm.Repr
      ensures cmm.Valid() && fresh(cmm.Repr - old(cmm.Repr))
    {
      var message := "Hello, World!!";
      var encodeResult := UTF8.Encode(message);
      expect encodeResult.Success?, "Failed to encode :( " + encodeResult.error + "\n";
      var encodedMsg := encodeResult.value;
      var encryptionContext := SmallEncryptionContext(SmallEncryptionContextVariation.A);
      var encryptRequest := new Client.EncryptRequest.WithCMM(encodedMsg, cmm);
      encryptRequest.SetEncryptionContext(encryptionContext);
      var e := Client.Encrypt(encryptRequest);
      if shouldFailGetClient {
        expect e.Failure?, "Successfully called GetClient when the call should have failed";
        return;
      }
      expect e.Success?, "Bad encryption :( " + e.error + "\n";

      var decryptRequest := new Client.DecryptRequest.WithCMM(e.value, cmm);
      var d := Client.Decrypt(decryptRequest);
      expect d.Success?, "bad decryption: " + d.error + "\n";

      expect UTF8.ValidUTF8Seq(d.value), "Could not decode Encryption output";
      var res :- expect UTF8.Decode(d.value);
      expect message == res;
    }

    method CreateTestingGenerator() returns (generator: KMSUtils.CustomerMasterKey)
    {
      var generatorStr := SHARED_TEST_KEY_ARN;
      expect KMSUtils.ValidFormatCMK(generatorStr);
      generator := generatorStr;
    }
  }

  method {:test} TestEndToEnd_BaseClientSupplier() {
    var clientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := ["some-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_NoRegions() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_Failure() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [CURRENT_REGION];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [CURRENT_REGION];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingExcludeRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var excludedRegions: seq<string> := ["some-excluded-region", "another-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, excludedRegions);
    var limitRegions: seq<string> := [CURRENT_REGION];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(excludeRegionsClientSupplier, limitRegions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_BadRegion() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := ["another-region"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_NoRegion() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_ConflictingExcludeSuppliers() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(limitRegionsClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingLimitRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var limitRegions: seq<string> := [CURRENT_REGION];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, limitRegions);
    var excludedRegions: seq<string> := ["some-excluded-region", "another-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(limitRegionsClientSupplier, excludedRegions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_Failure_ConflictingLimitSuppliers() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier(Option.None, Option.None);
    var regions: seq<string> := [CURRENT_REGION];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(excludeRegionsClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }
}
