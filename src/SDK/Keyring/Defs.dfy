include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"

  module KeyringDefs {
  import opened StandardLibrary
  import Materials
  import AlgorithmSuite

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(encMat: Materials.ValidEncryptionMaterialsInput) returns (res: Result<Option<Materials.ValidDataKey>>)
      requires Valid()
      ensures Valid()
      ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult(encMat, res.value.get)
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>)
      returns (res: Result<Option<Materials.ValidDataKey>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.encryptedDataKeys == edks
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
  }
}
