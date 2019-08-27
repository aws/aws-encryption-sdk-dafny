include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method OnEncrypt(x: EncryptionMaterials) returns (res: Result<EncryptionMaterials>)
      requires x.Valid()
      requires Valid()
      ensures Valid()
      ensures res.Ok? ==> res.get.Valid()
      ensures res.Ok? && x.plaintextDataKey.Some? ==> res.get.plaintextDataKey == x.plaintextDataKey
      ensures res.Ok? ==> res.get.algorithmSuiteID == x.algorithmSuiteID
      ensures res.Ok? ==> res.get.encryptionContext == x.encryptionContext
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance

    method OnDecrypt(x: DecryptionMaterials, encryptedDataKeys: seq<EncryptedDataKey>) returns (res: Result<DecryptionMaterials>)
      // TODO: Valid input DecMaterials
      requires Valid()
      ensures Valid()
      // TODO: Valid output DecMaterials
      ensures x.plaintextDataKey.Some? ==> res.Ok? && res.get == x
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
  }
}