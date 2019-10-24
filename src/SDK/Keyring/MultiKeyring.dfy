include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../Materials.dfy"

module MultiKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened Cipher
    import AlgorithmSuite
    import RSA = RSAEncryption
    import Mat = Materials

    function childrenRepr (xs : seq<Keyring>) : (res : set<object>) reads (set i | 0 <= i < |xs| :: xs[i])
        ensures forall i :: i in xs ==> i in res && i.Repr <= res
        decreases |xs|
    {
        if xs == [] then {} else
        childrenRepr(xs[1..]) + {xs[0]} + xs[0].Repr
    }

    class MultiKeyring extends Keyring {
        const generator : Keyring?
        const children : seq<Keyring>
        constructor (g : Keyring?, c : seq<Keyring>) ensures generator == g ensures children == c
            requires g != null ==> g.Valid()
            requires forall i :: 0 <= i < |c| ==> (c[i].Valid() && g !in c[i].Repr)
            ensures Valid()
        {
            generator := g;
            children := c;
            new;
            Repr := ReprDefn();
            assert (forall i :: 0 <= i < |c| ==> c[i] in Repr && c[i].Repr <= Repr);
        }

        predicate Valid() reads this, Repr {
            (generator != null ==> generator in Repr  && generator.Repr <= Repr && generator.Valid())  &&
            (forall j :: 0 <= j < |children| ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid()) &&
            Repr == ReprDefn() &&
            DisjointReprsRec({}, ChildKeyrings())
        }

        function ChildKeyrings(): seq<Keyring> reads generator, children {
            (if generator != null then [generator] else []) + children
        }

        function ReprDefn(): set<object> reads this, generator, children {
            {this} + (if generator != null then {generator} + generator.Repr else {}) + childrenRepr(children[..])
        }

        predicate DisjointReprsRec(r: set<object>, s: seq<Keyring>) 
                reads r, s, set i,o | 0 <= i < |s| && o in s[i].Repr :: o
                decreases |s|
        {
            if |s| == 0 then
                true
            else
                (r !! s[0].Repr) && DisjointReprsRec(r + s[0].Repr, s[1..])
        }

        method OnEncryptRec(input : Mat.ValidEncryptionMaterialsInput, output : seq<Mat.EncryptedDataKey>, i : int) returns (res: Result<seq<Mat.EncryptedDataKey>>)
            requires Valid()
            requires 0 <= i <= |children|
            ensures Valid()
            ensures forall i :: 0 <= i < |children| ==> children[i].Valid()
            decreases |children| - i
        {
            if i == |children| {
                return Success(output);
            }
            else {
                var y := children[i].OnEncrypt(input);
                assert generator != null ==> unchanged(generator);
                assert (generator != null ==> generator in Repr  && generator.Repr <= Repr && generator.Valid());
                match y {
                    case Success(r) => {
                        var a := OnEncryptRec(input, output + y.value.encryptedDataKeys, i + 1);
                        return a;
                    }
                    case Failure(e) => {
                        return Failure(e); 
                    }
                }

            }
        }

        method OnEncrypt(encMat : Mat.ValidEncryptionMaterialsInput) returns (res: Result<Mat.ValidEncryptionMaterialsOutput>)
            requires Valid()
            ensures Valid()
            ensures unchanged(Repr)
            ensures res.Success? ==> encMat.algorithmSuiteID == res.value.algorithmSuiteID
            ensures res.Success? && encMat.plaintextDataKey.Some? ==> res.value.plaintextDataKey == encMat.plaintextDataKey.get
        {
            var pdk := encMat.plaintextDataKey;
            if generator != null {
                var res := generator.OnEncrypt(encMat);
                match res {
                    case Success(a) => { pdk := Some(a.plaintextDataKey); }
                    case Failure(e) => { return Failure(e); }
                }
            }
            if pdk.None? {
                return Failure("Bad state: data key not found");
            }
            var edksResult := OnEncryptRec(encMat, [], 0);
            res := match edksResult {
                case Success(edks) => {
                    var output := Mat.EncryptionMaterialsOutput(encMat.algorithmSuiteID, pdk.get, edks, None);
                    if output.Valid() then Success(output) else Failure("What do??")
                }
                case Failure(error) => Failure("What do??")
            };
        }

        method OnDecryptRec(decMat : Mat.DecryptionMaterials, edks : seq<Mat.EncryptedDataKey>, i : int) returns (res : Result<Mat.DecryptionMaterials>)
            requires 0 <= i <= |children|
            requires Valid()
            requires decMat.Valid()
            ensures decMat.Valid()
            ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
            ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
            ensures res.Success? ==> res.value == decMat
            ensures res.Failure? ==> unchanged(decMat)
            //ensures res.Success? ==> res.value.algorithmSuiteID == decMat.algorithmSuiteID
            decreases |children| - i
        {

            if i == |children| {
                return Success(decMat);
            }
            else {
                var y := children[i].OnDecrypt(decMat, edks);
                match y {
                    case Success(r) => {
                        return Success(r);
                    }
                    case Failure(e) => {
                        res := OnDecryptRec(decMat, edks, i + 1);
                    }
                }

            }
        }

        method OnDecrypt(decMat : Mat.DecryptionMaterials, edks : seq<Mat.EncryptedDataKey>) returns (res : Result<Mat.DecryptionMaterials>)
            requires Valid()
            requires decMat.Valid()
            ensures Valid()
            ensures decMat.Valid()
            ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
            ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
            ensures res.Success? ==> res.value == decMat
            ensures res.Failure? ==> unchanged(decMat)
            //ensures res.Success? ==> res.value.algorithmSuiteID == encMat.algorithmSuiteID
        {
            var y := decMat;
            if generator != null {
                var r := generator.OnDecrypt(decMat, edks);
                match r  {
                    case Success(a) => { y := a; }
                    case Failure(f) => { }
                }
            }
            if y.plaintextDataKey.Some? {
                return Success(y);
            }
            var r := OnDecryptRec(y, edks, 0);
            match r {
                case Success(r) => {return Success(r);}
                case Failure(f) => {return Failure("multi ondecrypt Failure");} // TODO: percolate Failureors through like in C version
            }
        }
    }


}
