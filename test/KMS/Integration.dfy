// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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
  import opened Wrappers
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
      var encryptRequest := Client.EncryptRequest.WithCMM(encodedMsg, cmm).SetEncryptionContext(encryptionContext);
      var e := Client.Encrypt(encryptRequest);
      if shouldFailGetClient {
        expect e.Failure?, "Successfully called GetClient when the call should have failed";
        return;
      }
      expect e.Success?, "Bad encryption :( " + e.error + "\n";

      var decryptRequest := Client.DecryptRequest.WithCMM(e.value, cmm);
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

  method {:test} TestValidFormatCMKKeyARN() {
    var validArn := SHARED_TEST_KEY_ARN;

    expect KMSUtils.ValidFormatCMK("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    expect !KMSUtils.ValidFormatCMK("barn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
  }

  method {:test} TestEndToEnd_BaseClientSupplier() {
    var clientSupplier := new KMSUtils.BaseClientSupplier();
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["some-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_NoRegions() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_Failure() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [CURRENT_REGION];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [CURRENT_REGION];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingExcludeRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
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
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["another-region"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_NoRegion() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_ConflictingExcludeSuppliers() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(limitRegionsClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingLimitRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
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
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [CURRENT_REGION];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(excludeRegionsClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_CachingClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(baseClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
    expect |cachingClientSupplier.clientCache.ClientCache| == 1;
    expect cachingClientSupplier.clientCache.LookupClient(Some(CURRENT_REGION)).Some?;
  }

  method {:test} TestEndToEnd_CachingClientSupplier_ExcludeRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["another-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(excludeRegionsClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
    expect |cachingClientSupplier.clientCache.ClientCache| == 1;
    expect cachingClientSupplier.clientCache.LookupClient(Some(CURRENT_REGION)).Some?;
  }

  method {:test} TestEndToEnd_CachingClientSupplier_LimitRegionsClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [CURRENT_REGION];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(limitRegionsClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
    expect |cachingClientSupplier.clientCache.ClientCache| == 1;
    expect cachingClientSupplier.clientCache.LookupClient(Some(CURRENT_REGION)).Some?;
  }

  method {:test} TestEndToEnd_CachingClientSupplier_CachingClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var baseCachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(baseClientSupplier);
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(baseCachingClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, false);
    var lookupRegion := Some(CURRENT_REGION);
    expect |cachingClientSupplier.clientCache.ClientCache| == 1;
    expect cachingClientSupplier.clientCache.LookupClient(lookupRegion).Some?;
  }

  method {:test} TestEndToEnd_CachingClientSupplier_ExcludeRegionsClientSupplier_Failure() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := [CURRENT_REGION];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(excludeRegionsClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
    var lookupRegion := Some(CURRENT_REGION);
    expect cachingClientSupplier.clientCache.ClientCache == map[];
    expect cachingClientSupplier.clientCache.LookupClient(lookupRegion).None?;
  }

  method {:test} TestEndToEnd_CachingClientSupplier_LimitRegionsClientSupplier_Failure() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["another-region"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var cachingClientSupplier: KMSUtils.CachingClientSupplier := new KMSUtils.CachingClientSupplier(limitRegionsClientSupplier);
    var generator: KMSUtils.CustomerMasterKey := Helpers.CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(cachingClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    Helpers.EncryptDecryptTest(cmm, true);
    var lookupRegion := Some(CURRENT_REGION);
    expect cachingClientSupplier.clientCache.ClientCache == map[];
    expect cachingClientSupplier.clientCache.LookupClient(lookupRegion).None?;
  }
}
