include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(encMat: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys, encMat`keyringTrace
      ensures Valid()
      // Success returns a valid set of the modified input encryptionMaterials
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      // Failure does not modify the input encryptionMaterials
      ensures res.Failure? ==> unchanged(encMat)
      // If the encryptionMaterials contain a plaintextDataKey on input, it is unchanged
      ensures old(encMat.plaintextDataKey.Some?) ==> unchanged(encMat`plaintextDataKey)
      // New EDKs are only ever appended to the encryptedDataKeys
      ensures old(encMat.encryptedDataKeys) <= encMat.encryptedDataKeys
      // New traces are only ever appended to the keyringTrace
      ensures old(encMat.keyringTrace) <= encMat.keyringTrace
        
    method OnDecrypt(decMat: Materials.DecryptionMaterials, edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey, decMat`keyringTrace
      ensures Valid()
      // Success returns a valid set of the modified input decryptionMaterials
      ensures res.Success? ==> res.value.Valid() && res.value == decMat
      // If given an empty list of EDKs, returns Success and does not update the decryptionMaterials
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      // If input decryptionMaterials contain a plaintextDataKey,
      // returns Success and does not update the decryptionMaterials
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      // Failure does not modify the input encryptionMaterials
      ensures res.Failure? ==> unchanged(decMat)
      // New traces are only ever appended to the keyringTrace
      ensures old(decMat.keyringTrace) <= decMat.keyringTrace
  }
}
