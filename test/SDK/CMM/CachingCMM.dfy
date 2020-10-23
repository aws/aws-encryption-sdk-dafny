// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/SDK/CMM/Defs.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/SDK/Materials.dfy"
include "../../../src/Crypto/Signature.dfy"
include "../../../src/Util/Streams.dfy"
include "../../../src/SDK/Serialize.dfy"
include "../../../src/SDK/EncryptionContext.dfy"
include "../../../src/Util/Time.dfy"
include "../../../src/SDK/CMM/CachingCMM.dfy"
include "../../Util/TestUtils.dfy"
include "../../../src/Util/UTF8.dfy"

module TestCachingCMM {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import CachingCMMDef
  import Materials
  import AlgorithmSuite
  import EncryptionContext
  import TestUtils

  const SECONDS_TO_LIVE_LIMIT: nat := 3600  // for the tests

  /*
   * Tests of GetEncryptionMaterials
   */

  method {:test} TestGetEMMessagesLimit() {
    var tcmm := new Helpers.TestCMM();
    var messageLimit := 4;
    var byteLimit := 100;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, SECONDS_TO_LIVE_LIMIT, messageLimit, byteLimit);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));

    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cache hit at first, but entry gets evicted due to messageLimit, so it's effectively a miss
  }

  method {:test} TestGetEMBytesLimit() {
    var tcmm := new Helpers.TestCMM();
    var messageLimit := 1_000_000;
    var byteLimit := 100;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, SECONDS_TO_LIVE_LIMIT, messageLimit, byteLimit);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(29));

    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cold cache, 29 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);  // 58 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);  // 87 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cache hit, but entry gets evicted due to byteLimit, so tcmm is called again
  }

  method {:test} TestGetEMTimeLimit() {
    var tcmm := new Helpers.TestCMM();
    var ccmm := new CachingCMMDef.CachingCMM.ForTestingOnly_WithZeroTimeToLive(tcmm);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(29));

    // With a 0 time-to-live limit, everything will be a cache miss
    var n := 0;
    while n < 12
      invariant ccmm.Valid() && fresh(ccmm.Repr)
    {
      Helpers.CallGetEM(ccmm, tcmm, eRequest, false);
      n := n + 1;
    }
  }

  method {:test} TestGetEMVariationsInParameters() {
    var tcmm := new Helpers.TestCMM();
    var ccmm := new CachingCMMDef.CachingCMM(tcmm, SECONDS_TO_LIVE_LIMIT);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cold cache

    encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.BA);  // different order, shouldn't matter
    eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);

    var emptyEncryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.Empty);  // different map
    eRequest := Materials.EncryptionMaterialsRequest(emptyEncryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);

    // going back to a previous request
    eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);

    // plaintextLength does not affect the cache ID
    eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(99));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);

    eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG), Some(99));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);
  }

  /*
   * Tests of DecryptMaterials
   */

  method {:test} TestDMFlowLimit() {
    var tcmm := new Helpers.TestCMM();
    var messageLimit := 2;
    var byteLimit := 100;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, SECONDS_TO_LIVE_LIMIT, messageLimit, byteLimit);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.Empty);
    var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
    var dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    assert dRequest.Valid();

    // The limits on bytes and messages do not play a role for DecryptMaterials, so all of these
    // repeated calls will hit the cache
    var n := 0;
    while n < 12
      invariant ccmm.Valid() && fresh(ccmm.Repr)
    {
      Helpers.CallDM(ccmm, tcmm, dRequest, n != 0);
      n := n + 1;
    }
  }

  method {:test} TestDMTimeLimit() {
    var tcmm := new Helpers.TestCMM();
    var timeToLiveLimit := 1;
    var ccmm := new CachingCMMDef.CachingCMM.ForTestingOnly_WithZeroTimeToLive(tcmm);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
    var dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);

    // With a 0 time-to-live limit, everything will be a cache miss
    var n := 0;
    while n < 12
      invariant ccmm.Valid() && fresh(ccmm.Repr)
    {
      Helpers.CallDM(ccmm, tcmm, dRequest, false);
      n := n + 1;
    }
  }

  method {:test} TestDMVariationsInParameters() {
    var tcmm := new Helpers.TestCMM();
    var ccmm := new CachingCMMDef.CachingCMM(tcmm, SECONDS_TO_LIVE_LIMIT);

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.AB);
    var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
    var dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, false);  // cold cache

    encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.BA);  // different order, shouldn't matter
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, true);

    var emptyEncryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.Empty);  // different map
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], emptyEncryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, false);

    var edk' := Materials.EncryptedDataKey([], [82, 83], [84, 85]);  // different EDK
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk'], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, false);

    // going back to a previous request
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, true);
  }

  // To avoid a "Public method '...' should be marked as a Theory" warning from xUnit, these helper methods are
  // declared in their own module.
  module Helpers {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import CMMDefs
    import CachingCMMDef
    import Materials
    import EncryptionContext
    import AlgorithmSuite
    import UTF8
    import TestUtils

    // Call ccmm.GetEncryptionMaterial and report whether or not there was a cache hit
    method CallGetEM(ccmm: CachingCMMDef.CachingCMM, tcmm: TestCMM, request: Materials.EncryptionMaterialsRequest, expectCacheHit: bool)
      requires ccmm.Valid() && ccmm.cmm == tcmm
      requires EncryptionContext.Serializable(request.encryptionContext)
      requires request.encryptionContext.Keys !! Materials.RESERVED_KEY_VALUES
      modifies ccmm.Repr
      ensures ccmm.Valid() && fresh(ccmm.Repr - old(ccmm.Repr))
    {
      var previousECalls := tcmm.eCalls;
      var em :- expect ccmm.GetEncryptionMaterials(request);
      expect tcmm.eCalls == previousECalls || tcmm.eCalls == previousECalls + 1;
      expect expectCacheHit <==> tcmm.eCalls == previousECalls;
    }

    // Call ccmm.DecryptMaterials and report whether or not there was a cache hit
    method CallDM(ccmm: CachingCMMDef.CachingCMM, tcmm: TestCMM, request: Materials.ValidDecryptionMaterialsRequest, expectCacheHit: bool)
      requires ccmm.Valid() && ccmm.cmm == tcmm
      modifies ccmm.Repr
      ensures ccmm.Valid() && fresh(ccmm.Repr - old(ccmm.Repr))
    {
      var previousDCalls := tcmm.dCalls;
      var dm :- expect ccmm.DecryptMaterials(request);
      expect tcmm.dCalls == previousDCalls || tcmm.dCalls == previousDCalls + 1;
      expect expectCacheHit <==> tcmm.dCalls == previousDCalls;
    }

    /*
     * TestCMM is a dummy CMM that counts the number of calls to GetEncryptionMaterials and DecryptMaterials. This allows
     * the tests above to detect if the CachedCMM that wraps a TestCMM finds what it needs in the cache.
     */

    class TestCMM extends CMMDefs.CMM {
      var eCalls: nat
      var dCalls: nat
      predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
      {
        this in Repr
      }

      constructor ()
        ensures Valid() && fresh(Repr)
        ensures eCalls == dCalls == 0
      {
        eCalls, dCalls := 0, 0;
        Repr := {this};
      }

      method GetEncryptionMaterials(materialsRequest: Materials.EncryptionMaterialsRequest)
                                    returns (res: Result<Materials.ValidEncryptionMaterials>)
        requires Valid()
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.Serializable()
        ensures res.Success? ==> CMMDefs.EncryptionMaterialsSignature(res.value)
      {
        reveal CMMDefs.EncryptionMaterialsSignatureOpaque();
        TestUtils.ExpectSerializableEncryptionContext(materialsRequest.encryptionContext);

        var algSuiteID := if materialsRequest.algorithmSuiteID == None then AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 else materialsRequest.algorithmSuiteID.get;
        var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
        var tr0 := Materials.KeyringTraceEntry([], [], {Materials.GENERATED_DATA_KEY});
        var tr1 := Materials.KeyringTraceEntry([], [], {Materials.ENCRYPTED_DATA_KEY});
        var em := Materials.EncryptionMaterials(
          materialsRequest.encryptionContext,
          algSuiteID,
          Some(seq(algSuiteID.KDFInputKeyLength(), x => 70 + (x % 20) as uint8)), // plaintextDataKey
          [edk], // encryptedDataKeys
          [tr0, tr1], // keyringTrace
          if algSuiteID.SignatureType() == None then None else Some([52, 53, 54])); // signingKey
        assert em.Valid() by {
          calc {
            Filter([tr0, tr1], Materials.IsGenerateTraceEntry);
          ==  { assert Materials.IsGenerateTraceEntry(tr0); }
            [tr0] + Filter([tr0, tr1][1..], Materials.IsGenerateTraceEntry);
          ==  { assert [tr0, tr1][1..] == [tr1]; }
            [tr0] + Filter([tr1], Materials.IsGenerateTraceEntry);
          ==  // def. Filter
            [tr0];
          }
          assert Filter(em.keyringTrace, Materials.IsEncryptTraceEntry) == [tr1];
        }
        eCalls := eCalls + 1;
        return Success(em);
      }

      method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                              returns (res: Result<Materials.ValidDecryptionMaterials>)
        requires Valid()
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures res.Success? ==> res.value.plaintextDataKey.Some?
      {
        var dm := Materials.DecryptionMaterials(
          materialsRequest.algorithmSuiteID,
          materialsRequest.encryptionContext,
          Some(seq(materialsRequest.algorithmSuiteID.KDFInputKeyLength(), x => 70 + (x % 20) as uint8)), // plaintextDataKey
          Some([49, 48, 47]), // verificationKey
          []); // keyringTrace
        assert dm.Valid();
        dCalls := dCalls + 1;
        return Success(dm);
      }
    }
  }
}
