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
    predicate Valid() reads this, Repr

    method GetEncryptionMaterials(encCtx: Materials.EncryptionContext,
                                  algSuiteID: Option<AlgorithmSuite.ID>,
                                  plaintextLen: Option<nat>)
                                  returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() &&
                               res.value.plaintextDataKey.Some? && 
                               |res.value.plaintextDataKey.get| == res.value.algorithmSuiteID.KDFInputKeyLength() &&
                               |res.value.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some? &&
            Signature.ECDSA.WfSK(sigType, res.value.signingKey.get)

    // The following predicate is a synonym for MessageHeader.ValidAAD and provides a workaround for a translation bug
    // of "fuel" in trait-override checks in Dafny.
    predicate ValidAAD(encryptionContext: Materials.EncryptionContext) {
      MessageHeader.ValidAAD(encryptionContext)
    }

    method DecryptMaterials(algSuiteID: AlgorithmSuite.ID,
                            edks: seq<Materials.EncryptedDataKey>,
                            encCtx: Materials.EncryptionContext)
                            returns (res: Result<Materials.DecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() &&
                               res.value.plaintextDataKey.Some? &&
                               |res.value.plaintextDataKey.get| == res.value.algorithmSuiteID.KeyLength()
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
  }
}
