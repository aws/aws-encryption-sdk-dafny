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
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method GetEncryptionMaterials(encCtx: Materials.EncryptionContext,
                                  algSuiteID: Option<AlgorithmSuite.ID>,
                                  plaintextLen: Option<nat>)
                                  returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(encCtx) && Materials.GetKeysFromEncryptionContext(encCtx) !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> res.value.dataKeyMaterials.algorithmSuiteID.ValidPlaintextDataKey(res.value.dataKeyMaterials.plaintextDataKey)
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
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
  }
}
