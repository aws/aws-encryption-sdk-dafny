include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Common.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(encMat: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey
      modifies encMat`encryptedDataKeys
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Failure? ==> unchanged(encMat)
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance

    method OnDecrypt(decMat: Materials.DecryptionMaterials, edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      // TODO: Valid input DecMaterials
      modifies decMat`plaintextDataKey
      ensures Valid()
      // TODO: Valid output DecMaterials
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? &&
                                                res.value == decMat &&
                                                unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
  }
}
