include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "../Common.dfy"

module KeyringDefs {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import AlgorithmSuite
    import opened SDKDefs

    trait {:termination false} Keyring {
        ghost var Repr : set<object>
        predicate Valid() reads this, Repr

        method OnEncrypt(x : EncMaterials) returns (res : Result<EncMaterials>)
            requires WFEncMaterials(x)
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id

        method OnDecrypt(x : DecMaterials, edks : seq<EDK>) returns (res : Result<DecMaterials>)
            requires Valid()
            requires WFDecMaterials(x)
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id

    }

}
