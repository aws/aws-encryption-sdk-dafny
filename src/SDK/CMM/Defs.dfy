include "../Common.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"

module CMMDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite

  trait {:termination false} CMM {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

    method EncMatRequest(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()

    method DecMatRequest(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) returns (res: Result<Materials.DecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()
  }
}
