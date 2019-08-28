include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import opened Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(encMat: EncryptionMaterials) returns (res: Result<EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Success? ==> res.value.algorithmSuiteID == old(encMat.algorithmSuiteID)
      ensures res.Success? ==> res.value.encryptionContext == old(encMat.encryptionContext)
      ensures res.Success? ==> res.value.signingKey == old(encMat.signingKey)
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance

    method OnDecrypt(decMat: DecryptionMaterials, edks: seq<EncryptedDataKey>) returns (res: Result<DecryptionMaterials>)
      requires Valid()
      // TODO: Valid input DecMaterials
      modifies decMat
      ensures Valid()
      // TODO: Valid output DecMaterials
      ensures decMat.plaintextDataKey.Some? ==> res.Success? && res.value == decMat
      ensures res.Success? ==> res.value.algorithmSuiteID == old(decMat.algorithmSuiteID)
      ensures res.Success? ==> res.value.encryptionContext == old(decMat.encryptionContext)
      ensures res.Success? ==> res.value.verificationKey == old(decMat.verificationKey)
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
  }
}
