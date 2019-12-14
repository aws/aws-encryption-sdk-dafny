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
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

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
        var generateTraces := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
  }
}
