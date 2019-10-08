include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/GenBytes.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../Materials.dfy"

module MultiKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened Cipher
    import GenBytes = RNG
    import AlgorithmSuite
    import RSA = RSAEncryption
    import opened SDKDefs

    function childrenRepr (xs : seq<Keyring>) : (res : set<object>) reads (set i | 0 <= i < |xs| :: xs[i])
        ensures forall i :: i in xs ==> i in res && i.Repr <= res
    {
        if xs == [] then {} else
        childrenRepr(xs[1..]) + {xs[0]} + xs[0].Repr
    }

    class MultiKeyring extends Keyring {
        const generator : Keyring?
        const children : array<Keyring>
        constructor (g : Keyring?, c : array<Keyring>) ensures generator == g ensures children == c
            requires g != null ==> g.Valid()
            requires forall i :: 0 <= i < c.Length ==> c[i].Valid()
            ensures Valid()
        {
            generator := g;
            children := c;
            Repr := {this};
            new;
            if g != null {
                Repr := Repr + {g} + g.Repr;
            }
            Repr := Repr + {children} + childrenRepr(c[..]);
            assert (forall i :: 0 <= i < c.Length ==> c[i] in Repr && c[i].Repr <= Repr);

        }
        predicate Valid() reads this, Repr {
            children in Repr &&
            (generator != null ==> generator in Repr  && generator.Repr <= Repr && generator.Valid())  &&
            (forall j :: 0 <= j < children.Length ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid()) &&
            Repr == {this} + (if generator != null then {generator} + generator.Repr else {}) + {children} + childrenRepr(children[..])
        }

        method OnEncryptRec(x : EncMaterials, i : int) returns (res :Result<EncMaterials>)
            requires 0 <= i <= children.Length
            requires WFEncMaterials(x)
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
            decreases children.Length - i
        {
            if i == children.Length {
                return Ok(x);
            }
            else {
                var y := children[i].OnEncrypt(x);
                match y {
                    case Ok(r) => {
                        var a := OnEncryptRec(r, i + 1);
                        return a;
                    }
                    case Err(e) => {return Err(e); }
                }

            }
        }

        method OnEncrypt(x : EncMaterials) returns (res : Result<EncMaterials>)
            requires WFEncMaterials(x)
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
        {
            var r := x;
            if generator != null {
                var res := generator.OnEncrypt(x);
                match res {
                    case Ok(a) => { r := a; }
                    case Err(e) => {return Err(e); }
                }
            }
            if r.data_key.None? {
                return Err("Bad state: data key not found");
            }
            res := OnEncryptRec(r, 0);
        }

        method OnDecryptRec(x : DecMaterials, edks : seq<EDK>, i : int) returns (res : Result<DecMaterials>)
            requires 0 <= i <= children.Length
            requires Valid()
            requires WFDecMaterials(x)
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
            decreases children.Length - i
        {

            if i == children.Length {
                return Ok(x);
            }
            else {
                var y := children[i].OnDecrypt(x, edks);
                match y {
                    case Ok(r) => {
                        return Ok(r);
                    }
                    case Err(e) => {
                        res := OnDecryptRec(x, edks, i + 1);
                    }
                }

            }
        }

        method OnDecrypt(x : DecMaterials, edks : seq<EDK>) returns (res : Result<DecMaterials>)
            requires Valid()
            requires WFDecMaterials(x)
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
        {
            var y := x;
            if generator != null {
                var r := generator.OnDecrypt(x, edks);
                match r  {
                    case Ok(a) => { y := a; }
                    case Err(err) => { }
                }
            }
            if y.data_key.Some? {
                return Ok(y);
            }
            var r := OnDecryptRec(y, edks, 0);
            match r {
                case Ok(r) => {return Ok(r);}
                case Err(err) => {return Err("multi ondecrypt err");} // TODO: percolate errors through like in C version
            }
        }
    }


}
