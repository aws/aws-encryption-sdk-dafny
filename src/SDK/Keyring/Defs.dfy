include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"

module {:extern "KeyringDefs"} KeyringDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite

  trait {:termination false} Keyring {
    ghost const Repr : set<object>
    predicate Valid()

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures res.Success? && res.value.Some? ==> 
        algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
        plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==>
        var generateTraces: seq<Materials.KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0
      decreases Repr

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      decreases Repr

  }

  type ValidKeyring? = k: Keyring? | k == null || k.Valid()

  trait {:extern} ExternalKeyring {
    ghost const Repr : set<object>;

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
        decreases Repr

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
        decreases Repr
  }

  class AsExternalKeyring extends ExternalKeyring {
    const wrapped: ValidKeyring?;
    constructor(wrapped: ValidKeyring?) 
        requires wrapped != null
        ensures Valid() 
        ensures fresh(Repr - {wrapped} - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }

    predicate Valid() {
        && this in Repr 
        && wrapped in Repr 
        && wrapped.Repr <= Repr 
        && this !in wrapped.Repr
        && wrapped.Valid()
    }

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Materials.ValidDataKeyMaterials>>) 
      decreases Repr
    {
      var _ :- Require(wrapped != null);
      var _ :- Require(plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get));
      res := wrapped.OnEncrypt(algorithmSuiteID, encryptionContext, plaintextDataKey);
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      decreases Repr 
    {
      var _ :- Require(wrapped != null);
      res := wrapped.OnDecrypt(algorithmSuiteID, encryptionContext, edks);
    }
  }

  class AsKeyring extends Keyring {
    const wrapped: ExternalKeyring;

    constructor(wrapped: ExternalKeyring) {
      this.wrapped := wrapped;
    }

    predicate Valid() {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
    }

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Materials.ValidDataKeyMaterials>>) 
      requires Valid()
      ensures res.Success? && res.value.Some? ==> 
        algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
        plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==>
        var generateTraces: seq<Materials.KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0
      decreases Repr
    {
      res := wrapped.OnEncrypt(algorithmSuiteID, encryptionContext, plaintextDataKey);
      var _ :- Require(res.Success? && res.value.Some? ==> 
          algorithmSuiteID == res.value.get.algorithmSuiteID);
      var _ :- Require(res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
          plaintextDataKey.get == res.value.get.plaintextDataKey);
      var _ :- Require(res.Success? && res.value.Some? ==>
        var generateTraces: seq<Materials.KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0);
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<Materials.ValidOnDecryptResult>>) 
      requires Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      decreases Repr
    {
      if |edks| == 0 {
        return Success(None);
      }
      res := wrapped.OnDecrypt(algorithmSuiteID, encryptionContext, edks);
      var _ :- Require(res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID);
    }
  }
}
