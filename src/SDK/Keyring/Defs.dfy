include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite

  // TODO Seems a bit strange to have this defined here but ValidDataKeyMaterials elsewhere, however this is defining logic
  // specific to keyrings so it might seem misplaced in Materials.dfy
  // TODO 'res' is already a common name for the out param, so naming this Result might be overloading the term
  datatype OnDecryptResult = OnDecryptResult(algorithmSuiteID: AlgorithmSuite.ID,
                                             plaintextDataKey: seq<uint8>,
                                             keyringTrace: seq<Materials.KeyringTraceEntry>) // TODO does it make sense to define this as a sequence when we are requiring only one for now?
  {
    predicate Valid() {
      && algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      && (forall trace :: trace in keyringTrace ==> trace.flags <= Materials.ValidDecryptionMaterialFlags)
      && |keyringTrace| == 1 && Materials.IsDecryptTrace(keyringTrace[0])
    }

    static function method ValidWitness(): OnDecryptResult {
      var pdk := seq(32, i => 0);
      var trace := Materials.KeyringTraceEntry([], [], {Materials.DECRYPTED_DATA_KEY});
      var r := OnDecryptResult(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                      pdk, [trace]);
      r
    }
  }

  type ValidOnDecryptResult = i: OnDecryptResult | i.Valid() witness OnDecryptResult.ValidWitness()

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
      // TODO: Is there any way we can move the below logic into the dataKeyMaterials itself? Or does that not make sense functionally?
      ensures res.Success? && res.value.Some? && plaintextDataKey.None? ==>
        var generateTraces := Filter(res.value.get.keyringTrace, Materials.IsGenerateTrace);
        |generateTraces| == 1
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==>
        var generateTraces := Filter(res.value.get.keyringTrace, Materials.IsGenerateTrace);
        |generateTraces| == 0

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
  }
}
