include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../Crypto/Signature.dfy"
include "../MessageHeader.dfy"

module CMMDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Signature
  import MessageHeader

  trait {:termination false} CMM {
    ghost var Repr : set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method GetEncryptionMaterials(encCtx: Materials.EncryptionContext,
                                  algSuiteID: Option<AlgorithmSuite.ID>,
                                  plaintextLen: Option<nat>)
                                  returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(encCtx) && Materials.GetKeysFromEncryptionContext(encCtx) !! Materials.ReservedKeyValues
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> |res.value.dataKeyMaterials.plaintextDataKey| == res.value.dataKeyMaterials.algorithmSuiteID.KDFInputKeyLength()
      ensures res.Success? ==> |res.value.dataKeyMaterials.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.dataKeyMaterials.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some? &&
            Signature.ECDSA.WfSK(sigType, res.value.signingKey.get)

    // The following predicate is a synonym for MessageHeader.ValidAAD and provides a workaround for a translation bug
    // of "fuel" in trait-override checks in Dafny. https://github.com/dafny-lang/dafny/issues/422
    predicate ValidAAD(encryptionContext: Materials.EncryptionContext) {
      MessageHeader.ValidAAD(encryptionContext)
    }

    method DecryptMaterials(algSuiteID: AlgorithmSuite.ID,
                            edks: seq<Materials.EncryptedDataKey>,
                            encCtx: Materials.EncryptionContext)
                            returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid() && ValidAAD(encCtx) && |edks| > 0
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==>
        |res.value.plaintextDataKey| == res.value.algorithmSuiteID.KeyLength()
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
  }
}
