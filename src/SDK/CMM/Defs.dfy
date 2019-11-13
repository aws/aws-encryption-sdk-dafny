include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../Crypto/Signature.dfy"

module CMMDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Signature

  trait {:termination false} CMM {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method GetEncryptionMaterials(encCtx: Materials.EncryptionContext,
                                  algSuiteID: Option<AlgorithmSuite.ID>,
                                  plaintextLen: Option<nat>)
                                  returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> |res.value.dataKeyMaterials.encryptedDataKeys| > 0
      ensures res.Success? ==>
        match res.value.dataKeyMaterials.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some? &&
            Signature.ECDSA.WfSK(sigType, res.value.signingKey.get)

    method DecryptMaterials(algSuiteID: AlgorithmSuite.ID,
                            edks: seq<Materials.EncryptedDataKey>,
                            encCtx: Materials.EncryptionContext)
                            returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
  }
}
