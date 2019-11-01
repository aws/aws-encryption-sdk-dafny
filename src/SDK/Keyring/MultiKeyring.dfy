include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../Materials.dfy"

module MultiKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
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
            requires forall i :: 0 <= i < |c| ==> c[i].Valid()
            requires PairwiseDisjoint(MapSeq(ChildKeyrings(g, c), (k: Keyring) reads k, k.Repr => k.Repr))
            ensures Valid()
        {
            generator := g;
            children := c;
            new;
            Repr := ReprDefn();
        }

        predicate Valid() reads this, Repr {
            (generator != null ==> generator in Repr  && generator.Repr <= Repr && generator.Valid())  &&
            (forall j :: 0 <= j < |children| ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid()) &&
            Repr == ReprDefn() &&
            PairwiseDisjoint(MapSeq(ChildKeyrings(generator, children), (k: Keyring) reads k, k.Repr => k.Repr))
        }

        static function ChildKeyrings(g: Keyring?, c: seq<Keyring>): seq<Keyring> {
            (if g != null then [g] else []) + c
        }

        static function ChildReprs(g: Keyring?, c: seq<Keyring>): seq<set<object>> 
            reads g, c, (if g != null then g.Repr else {}), set i,o | 0 <= i < |c| && o in c[i].Repr :: o
        {
            MapSeq(ChildKeyrings(g, c), (k: Keyring) reads k, k.Repr => k.Repr)
        }

        function ReprDefn(): set<object> reads this, generator, children {
            {this} + (if generator != null then {generator} + generator.Repr else {}) + childrenRepr(children[..])
        }

        method OnEncryptRec(input: Mat.ValidEncryptionMaterialsInput, output: Mat.ValidDataKey, i: int) returns (res: Result<Mat.ValidDataKey>)
            requires Valid()
            requires 0 <= i <= |children|
            requires Mat.ValidOnEncryptResult(input, output)
            requires input.plaintextDataKey.Some? && input.plaintextDataKey.get == output.plaintextDataKey
            ensures Valid()
            ensures forall i :: 0 <= i < |children| ==> children[i].Valid()
            ensures res.Success? ==> Mat.ValidOnEncryptResult(input, res.value)
            decreases |children| - i
        {
            if i == |children| {
                return Success(output);
            }
            else {
                var r :- children[i].OnEncrypt(input);
                if r.Some? {
                    Materials.ValidOnEncryptResultImpliesSameAlgorithmSuiteID(input, r.get);
                }
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
            ensures res.Success? && res.value.Some? ==> Materials.ValidOnEncryptResult(encMat, res.value.get)
        {
            var initialDataKey: Option<Mat.ValidDataKey> := None;
            if encMat.plaintextDataKey.Some? {
                initialDataKey := Some(Mat.DataKey(encMat.algorithmSuiteID, encMat.plaintextDataKey.get, []));
            }
            
            if generator != null {
                initialDataKey :- generator.OnEncrypt(encMat);
                if initialDataKey.Some? {
                    Materials.ValidOnEncryptResultImpliesSameAlgorithmSuiteID(encMat, initialDataKey.get);
                }
            }
            if initialDataKey.None? {
                return Failure("Bad state: data key not found");
            }
            var input := Mat.EncryptionMaterialsInput(encMat.algorithmSuiteID, encMat.encryptionContext, Some(initialDataKey.get.plaintextDataKey));
            var result :- OnEncryptRec(input, initialDataKey.get, 0);
            res := Success(Some(result));
        }

        method OnDecryptRec(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>, i : int)
            returns (res: Result<Option<Materials.ValidDataKey>>)
            requires 0 <= i <= |children|
            requires Valid()
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && res.value.None?
            ensures res.Success? && res.value.Some? ==> 
                Materials.ValidOnDecryptResult(algorithmSuiteID, encryptionContext, edks, res.value.get)
            decreases |children| - i
        {
            if i == |children| {
                return Success(None);
            } else {
                var y := children[i].OnDecrypt(algorithmSuiteID, encryptionContext, edks);
                match y {
                    case Success(result) =>
                        if result.Some? {
                            return y;
                        }
                    // TODO-RS: If all keyrings fail, pass on at least one of the errors,
                    // preferrably all of them in a chain of some kind.
                    case Failure(_) => {}
                }
                res := OnDecryptRec(algorithmSuiteID, encryptionContext, edks, i + 1);
            }
        }

        method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>)
            returns (res: Result<Option<Materials.ValidDataKey>>)
            requires Valid()
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && res.value.None?
            ensures res.Success? && res.value.Some? ==> 
                Materials.ValidOnDecryptResult(algorithmSuiteID, encryptionContext, edks, res.value.get)
        {
            if generator != null {
                var result :- generator.OnDecrypt(algorithmSuiteID, encryptionContext, edks);
                if result.Some? {
                    return Success(result);
                }
            }
            res := OnDecryptRec(algorithmSuiteID, encryptionContext, edks, 0);
        }
    }
}
