include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/Crypto/Signature.dfy"
include "../../src/Util/Streams.dfy"
include "../../src/SDK/Serialize.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/Util/Time.dfy"
include "../../src/SDK/CMM/CachingCMM.dfy"
include "../Util/TestUtils.dfy"
include "../../src/Util/UTF8.dfy"

module TestCachingCMM {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import CachingCMMDef
  import Materials
  import AlgorithmSuite
  import EncryptionContext
  import TestUtils
  import UTF8

  /*
   * Tests of GetEncryptionMaterials
   */
  
  method {:test} TestGetEMMessagesLimit() {
    var tcmm := new Helpers.TestCMM();
    var bytesLimit := 100;
    var messagesLimit := 4;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, CachingCMMDef.DEFAULT_SECONDS_TO_LIVE_LIMIT, bytesLimit, messagesLimit);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));

    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cache hit at first, but entry gets evicted due to messagesLimit, so it's effectively a miss
  }

  method {:test} TestGetEMBytesLimit() {
    var tcmm := new Helpers.TestCMM();
    var bytesLimit := 100;
    var messagesLimit := 1_000_000;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, CachingCMMDef.DEFAULT_SECONDS_TO_LIVE_LIMIT, bytesLimit, messagesLimit);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(29));

    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cold cache, 29 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);  // 58 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);  // 87 bytes total
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cache hit, but entry gets evicted due to bytesLimit, so tcmm is called again
  }

  method {:test} TestGetEMTimeLimit() {
    var tcmm := new Helpers.TestCMM();
    var timeToLiveLimit := 0;
    var bytesLimit := 1_000_000;
    var messagesLimit := 1_000_000;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, timeToLiveLimit, bytesLimit, messagesLimit);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(29));

    // With a time-to-live limit of 0, everything will be a cache miss
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
    var ccmm := new CachingCMMDef.CachingCMM(tcmm);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, false);  // cold cache

    encryptionContext := map[keyB := valB, keyA := valA];  // different order, shouldn't matter
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    eRequest := Materials.EncryptionMaterialsRequest(encryptionContext, Some(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Some(5));
    Helpers.CallGetEM(ccmm, tcmm, eRequest, true);

    var emptyEncryptionContext := map[];  // different map
    TestUtils.ValidSmallEncryptionContext(emptyEncryptionContext);
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
    var bytesLimit := 100;
    var messagesLimit := 2;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, CachingCMMDef.DEFAULT_SECONDS_TO_LIVE_LIMIT, bytesLimit, messagesLimit);

    var encryptionContext := map[];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
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
    var timeToLiveLimit := 0;
    var bytesLimit := 1_000_000;
    var messagesLimit := 1_000_000;
    var ccmm := new CachingCMMDef.CachingCMM.WithLimits(tcmm, timeToLiveLimit, bytesLimit, messagesLimit);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
    var dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);

    // With a time-to-live limit of 0, everything will be a cache miss
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
    var ccmm := new CachingCMMDef.CachingCMM(tcmm);

    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyA := valA, keyB := valB];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    var edk: Materials.ValidEncryptedDataKey := Materials.EncryptedDataKey([], [], []);
    var dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, false);  // cold cache

    encryptionContext := map[keyB := valB, keyA := valA];  // different order, shouldn't matter
    TestUtils.ValidSmallEncryptionContext(encryptionContext);
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, true);

    var emptyEncryptionContext := map[];  // different map
    TestUtils.ValidSmallEncryptionContext(emptyEncryptionContext);
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], emptyEncryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, false);

    // going back to a previous request
    dRequest := Materials.DecryptionMaterialsRequest(AlgorithmSuite.AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, [edk], encryptionContext);
    Helpers.CallDM(ccmm, tcmm, dRequest, true);

    // the cache is insensitive to the given list of EDKs, so changing the EDK should still give a cache hit
    edk := Materials.EncryptedDataKey([], [82, 83], [84, 85]);
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

    // Call ccmm.GetEncryptionMaterial and report whether or not there was a cache hit
    method CallGetEM(ccmm: CachingCMMDef.CachingCMM, tcmm: TestCMM, request: Materials.EncryptionMaterialsRequest, expectCacheHit: bool)
      requires ccmm.Valid() && ccmm.cmm == tcmm
      requires EncryptionContext.Valid(request.encryptionContext)
      requires request.encryptionContext.Keys !! Materials.ReservedKeyValues
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
        requires ValidAAD(materialsRequest.encryptionContext)
        requires materialsRequest.encryptionContext.Keys !! Materials.ReservedKeyValues
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
        ensures res.Success? ==> |res.value.encryptedDataKeys| > 0
        ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
        ensures res.Success? ==>
          match res.value.algorithmSuiteID.SignatureType()
            case None => true
            case Some(sigType) =>
              res.value.signingKey.Some?
      {
        var algSuiteID := if materialsRequest.algorithmSuiteID == None then AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 else materialsRequest.algorithmSuiteID.get;
        var edk: Materials.ValidEncryptedDataKey;// := EncryptedDataKey([], [], []);
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
        ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
        ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
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
