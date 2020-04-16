include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../Crypto/Signature.dfy"
include "../EncryptionContext.dfy"

module {:extern "CMMDefs"} CMMDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Signature
  import EncryptionContext

  trait {:termination false} CMM {
    ghost var Repr: set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method GetEncryptionMaterials(materialsRequest: Materials.EncryptionMaterialsRequest)
                                  returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(materialsRequest.encryptionContext)
      requires materialsRequest.encryptionContext.Keys !! Materials.RESERVED_KEY_VALUES
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.Serializable()

    // The following predicate is a synonym for Encryption.Serializable and provides a workaround for a translation bug
    // of "fuel" in trait-override checks in Dafny. https://github.com/dafny-lang/dafny/issues/422
    static predicate ValidAAD(encryptionContext: EncryptionContext.Map) {
      EncryptionContext.Serializable(encryptionContext)
    }

    method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                            returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
  }
}
