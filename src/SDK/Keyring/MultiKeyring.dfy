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

        method OnEncryptRec(input: Mat.ValidEncryptionMaterialsInput, output: Mat.ValidDataKey, i: int) returns (res: Result<Mat.ValidDataKey>)
            requires Valid()
            requires 0 <= i <= |children|
            requires Mat.ValidOnEncryptResult1(input, output)
            requires Mat.ValidOnEncryptResult2(input, output)
            requires input.plaintextDataKey.Some? && input.plaintextDataKey.get == output.plaintextDataKey
            ensures Valid()
            ensures forall i :: 0 <= i < |children| ==> children[i].Valid()
            ensures res.Success? ==> Mat.ValidOnEncryptResult1(input, res.value)
            ensures res.Success? ==> Mat.ValidOnEncryptResult2(input, res.value)
            decreases |children| - i
        {
            if i == |children| {
                return Success(output);
            }
            else {
                var r :- children[i].OnEncrypt(input);
                var newOutput := if r.Some? then
                    Mat.MergingResults(input, output, r.get);
                    Mat.MergeDataKeys(output, r.get) 
                else output;
                var a := OnEncryptRec(input, newOutput, i + 1);
                return a;
            }
        }

        method OnEncrypt(encMat : Mat.ValidEncryptionMaterialsInput) returns (res: Result<Option<Mat.ValidDataKey>>)
            requires Valid()
            ensures Valid()
            ensures unchanged(Repr)
            ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult1(encMat, res.value.get)
            ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult2(encMat, res.value.get)
        {
            var initialDataKey := if encMat.plaintextDataKey.Some? then Some(Mat.DataKey(encMat.algorithmSuiteID, encMat.plaintextDataKey.get, [])) else None;
            if generator != null {
                initialDataKey :- generator.OnEncrypt(encMat);
            }
            if initialDataKey.None? {
                return Failure("Bad state: data key not found");
            }
            var input := Mat.EncryptionMaterialsInput(encMat.algorithmSuiteID, encMat.encryptionContext, Some(initialDataKey.get.plaintextDataKey));
            var result :- OnEncryptRec(input, initialDataKey.get, 0);
            res := Success(Some(result));
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
            // if generator != null {
            //     var r := generator.OnDecrypt(decMat, edks);
            //     match r  {
            //         case Success(a) => { y := a; }
            //         case Failure(f) => { }
            //     }
            // }
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
