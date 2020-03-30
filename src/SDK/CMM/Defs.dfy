include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../Crypto/Signature.dfy"
include "../MessageHeader.dfy"

module {:extern "CMMDefs"} CMMDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Signature
  import MessageHeader

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
      ensures Valid()
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? ==> |res.value.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some?

    // The following predicate is a synonym for MessageHeader.ValidAAD and provides a workaround for a translation bug
    // of "fuel" in trait-override checks in Dafny. https://github.com/dafny-lang/dafny/issues/422
    predicate ValidAAD(encryptionContext: Materials.EncryptionContext) {
      MessageHeader.ValidAAD(encryptionContext)
    }

    method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                            returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
  }
}
