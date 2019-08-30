include "../Common.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"

module CMMDefs {
    import opened SDKDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import AlgorithmSuite

    trait {:termination false} CMM {
        ghost var Repr : set<object>
        predicate Valid() reads this, Repr

        method EncMatRequest(ec : EncCtx, alg_id : Option<AlgorithmSuite.ID>, pt_len : Option<nat>) returns (res : Result<EncMaterials>)
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)

        method DecMatRequest(alg_id : AlgorithmSuite.ID, edks : seq<EDK>, enc_ctx : EncCtx) returns (res : Result<DecMaterials>)
            requires |edks| > 0
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
    }



}