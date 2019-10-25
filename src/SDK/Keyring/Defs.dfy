include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(encMat: Materials.ValidEncryptionMaterialsInput) returns (res: Result<Option<Materials.ValidDataKey>>)
      requires Valid()
      ensures Valid()
      ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult1(encMat, res.value.get)
      ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult2(encMat, res.value.get)
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance

    method OnDecrypt(decMat: Materials.DecryptionMaterials, edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey
      ensures Valid()
      ensures decMat.Valid()
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
  }
}
