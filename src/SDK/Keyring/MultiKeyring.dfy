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
    import Mat = Materials

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

        method OnEncryptRec(x : Mat.EncryptionMaterials, i : int) returns (res: Result<Mat.EncryptionMaterials>)
            requires 0 <= i <= children.Length
            requires x.Valid()
            requires Valid()
            ensures Valid()
            ensures res.Success? ==> res.value.Valid()
            ensures res.Success? ==> res.value.algorithmSuiteID == x.algorithmSuiteID
            decreases children.Length - i
        {
            if i == children.Length {
                return Success(x);
            }
            else {
                var y := children[i].OnEncrypt(x);
                match y {
                    case Success(r) => {
                        var a := OnEncryptRec(r, i + 1);
                        return a;
                    }
                    case Failure(e) => {return Failure(e); }
                }

            }
        }

        method OnEncrypt(x : Mat.EncryptionMaterials) returns (res : Result<Mat.EncryptionMaterials>)
            requires x.Valid()
            requires Valid()
            ensures Valid()
            ensures res.Success? ==> res.value.Valid()
            ensures res.Success? ==> res.value.algorithmSuiteID == x.algorithmSuiteID
        {
            var r := x;
            if generator != null {
                var res := generator.OnEncrypt(x);
                match res {
                    case Success(a) => { r := a; }
                    case Failure(e) => {return Failure(e); }
                }
            }
            if r.plaintextDataKey.None? {
                return Failure("Bad state: data key not found");
            }
            res := OnEncryptRec(r, 0);
        }

        method OnDecryptRec(x : Mat.DecryptionMaterials, edks : seq<Mat.EncryptedDataKey>, i : int) returns (res : Result<Mat.DecryptionMaterials>)
            requires 0 <= i <= children.Length
            requires Valid()
            requires x.Valid()
            ensures Valid()
            ensures res.Success? ==> res.value.Valid()
            ensures res.Success? ==> res.value.algorithmSuiteID == x.algorithmSuiteID
            decreases children.Length - i
        {

            if i == children.Length {
                return Success(x);
            }
            else {
                var y := children[i].OnDecrypt(x, edks);
                match y {
                    case Success(r) => {
                        return Success(r);
                    }
                    case Failure(e) => {
                        res := OnDecryptRec(x, edks, i + 1);
                    }
                }

            }
        }

        method OnDecrypt(x : Mat.DecryptionMaterials, edks : seq<Mat.EncryptedDataKey>) returns (res : Result<Mat.DecryptionMaterials>)
            requires Valid()
            requires x.Valid()
            ensures Valid()
            ensures res.Success? ==> res.value.Valid()
            ensures res.Success? ==> res.value.algorithmSuiteID == x.algorithmSuiteID
        {
            var y := x;
            if generator != null {
                var r := generator.OnDecrypt(x, edks);
                match r  {
                    case Success(a) => { y := a; }
                    case Failure(err) => { }
                }
            }
            if y.plaintextDataKey.Some? {
                return Success(y);
            }
            var r := OnDecryptRec(y, edks, 0);
            match r {
                case Success(r) => {return Success(r);}
                case Failure(err) => {return Failure("multi ondecrypt err");} // TODO: percolate errors through like in C version
            }
        }
    }


}
