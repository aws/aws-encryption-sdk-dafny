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
            requires AllKeyringsDisjoint(g, c)
            ensures Valid()
        {
            generator := g;
            children := c;
            new;
            Repr := ReprDefn();
        }

        predicate Valid() reads this, Repr {
            (generator != null ==> generator in Repr && generator.Repr <= Repr && generator.Valid())  &&
            (forall j :: 0 <= j < |children| ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid()) &&
            Repr == ReprDefn() &&
            AllKeyringsDisjoint(generator, children)
        }

        static predicate AllKeyringsDisjoint(g: Keyring?, c: seq<Keyring>) 
            reads g, c, (if g != null then g.Repr else {}), set i,o | 0 <= i < |c| && o in c[i].Repr :: o
        {
            var keyrings: seq<Keyring> := (if g != null then [g] else []) + c;
            PairwiseDisjoint(MapSeq(keyrings, (k: Keyring) reads k, k.Repr => k.Repr))
        }

        function ReprDefn(): set<object> reads this, generator, children {
            {this} + (if generator != null then {generator} + generator.Repr else {}) + childrenRepr(children[..])
        }

        method OnEncryptRec(encryptionContext: Mat.EncryptionContext,
                            output: Mat.ValidDataKey, i: int) returns (res: Result<Mat.ValidDataKey>)
            requires Valid()
            requires 0 <= i <= |children|
            ensures Valid()
            ensures forall i :: 0 <= i < |children| ==> children[i].Valid()
            ensures res.Success? ==> 
                output.plaintextDataKey == res.value.plaintextDataKey
            ensures res.Success? ==> 
                output.algorithmSuiteID == res.value.algorithmSuiteID
            decreases |children| - i
        {
            if i == |children| {
                return Success(output);
            }
            else {
                var r :- children[i].OnEncrypt(output.algorithmSuiteID, encryptionContext, Some(output.plaintextDataKey));
                var newOutput := if r.Some? then Mat.MergeDataKeys(output, r.get) else output;
                var a := OnEncryptRec(encryptionContext, newOutput, i + 1);
                return a;
            }
        }

        method OnEncrypt(algorithmSuiteID: Mat.AlgorithmSuite.ID,
                         encryptionContext: Mat.EncryptionContext,
                         plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Mat.ValidDataKey>>)
            requires Valid()
            requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
            ensures Valid()
            ensures unchanged(Repr)
            ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
                plaintextDataKey.get == res.value.get.plaintextDataKey
            ensures res.Success? && res.value.Some? ==> 
                algorithmSuiteID == res.value.get.algorithmSuiteID
        {
            var initialDataKey: Option<Mat.ValidDataKey> := None;
            if plaintextDataKey.Some? {
                initialDataKey := Some(Mat.DataKey(algorithmSuiteID, plaintextDataKey.get, []));
            }
            
            if generator != null {
                initialDataKey :- generator.OnEncrypt(algorithmSuiteID, encryptionContext, plaintextDataKey);
                if initialDataKey.Some? {
                    assert initialDataKey.get.algorithmSuiteID == algorithmSuiteID;
                    assert algorithmSuiteID.ValidPlaintextDataKey(initialDataKey.get.plaintextDataKey);
                }
            }
            if initialDataKey.None? {
                return Failure("Bad state: data key not found");
            }
            var result :- OnEncryptRec(encryptionContext, initialDataKey.get, 0);
            res := Success(Some(result));
        }

        method OnDecryptRec(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>, i : int)
            returns (res: Result<Option<seq<uint8>>>)
            requires 0 <= i <= |children|
            requires Valid()
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && res.value.None?
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

        method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     edks: seq<Mat.EncryptedDataKey>) 
            returns (res: Result<Option<seq<uint8>>>)
            requires Valid() 
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && res.value.None?
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
