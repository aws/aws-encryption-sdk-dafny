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
        // TODO-RS: Make this a seq<Keyring> once https://github.com/dafny-lang/dafny/issues/406 is addressed
        const children : array<Keyring>
        constructor (g : Keyring?, c : array<Keyring>) ensures generator == g ensures children == c
            requires g != null ==> g.Valid()
            requires forall i :: 0 <= i < c.Length ==> c[i].Valid()
            ensures Valid()
        {
            generator := g;
            children := c;
            Repr := {this} + (if g != null then {g} + g.Repr else {}) + {children} + childrenRepr(c[..]);
        }

        predicate Valid() reads this, Repr {
            && children in Repr
            && (generator != null ==> generator in Repr && generator.Repr <= Repr && generator.Valid())
            && (forall j :: 0 <= j < children.Length ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid())
        }

        method OnEncrypt(algorithmSuiteID: Mat.AlgorithmSuite.ID,
                         encryptionContext: Mat.EncryptionContext,
                         plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Mat.ValidDataKeyMaterials>>)
            requires Valid()
            requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
            ensures Valid()
            ensures unchanged(Repr)
            ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
                plaintextDataKey.get == res.value.get.plaintextDataKey
            ensures res.Success? && res.value.Some? ==> 
                algorithmSuiteID == res.value.get.algorithmSuiteID
        {
            // First pass on or generate the plaintext data key
            var initialMaterials: Option<Mat.ValidDataKeyMaterials> := None;
            if plaintextDataKey.Some? {
                initialMaterials := Some(Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey.get, []));
            }
            if generator != null {
                initialMaterials :- generator.OnEncrypt(algorithmSuiteID, encryptionContext, plaintextDataKey);
            }
            if initialMaterials.None? {
                return Failure("Bad state: data key not found");
            }

            // Then apply each of the children in sequence
            // TODO-RS: Use folding here instead
            var resultMaterials := initialMaterials.get;
            var i := 0;
            while (i < children.Length) 
                invariant algorithmSuiteID == resultMaterials.algorithmSuiteID
                invariant plaintextDataKey.Some? ==> plaintextDataKey.get == resultMaterials.plaintextDataKey
                decreases children.Length - i 
            {
                var childResult :- children[i].OnEncrypt(resultMaterials.algorithmSuiteID, encryptionContext, Some(resultMaterials.plaintextDataKey));
                if childResult.Some? {
                    resultMaterials := Mat.MergeDataKeyMaterials(resultMaterials, childResult.get);
                }
                i := i + 1;
            }
            res := Success(Some(resultMaterials));
        }
        method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                         encryptionContext: Mat.EncryptionContext,
                         edks: seq<Mat.EncryptedDataKey>) 
            returns (res: Result<Option<seq<uint8>>>)
            requires Valid() 
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && res.value.None?
            ensures res.Success? && res.value.Some? ==> 
                algorithmSuiteID.ValidPlaintextDataKey(res.value.get)
        {
            res := Success(None);
            if generator != null {
                var plaintextDataKey := TryDecryptForKeyring(generator, algorithmSuiteID, encryptionContext, edks);
                if plaintextDataKey.Some? {
                    res := Success(plaintextDataKey);
                }
            }
            var i := 0;
            while (i < children.Length) 
                invariant |edks| == 0 ==> res.Success? && res.value.None?
                invariant res.Success? && res.value.Some? ==> 
                    algorithmSuiteID.ValidPlaintextDataKey(res.value.get)
                decreases children.Length - i
            {
                var plaintextDataKey := TryDecryptForKeyring(children[i], algorithmSuiteID, encryptionContext, edks);
                if plaintextDataKey.Some? {
                    res := Success(plaintextDataKey);
                }
                i := i + 1;
            }
        }

        method TryDecryptForKeyring(keyring: Keyring,
                                    algorithmSuiteID: AlgorithmSuite.ID,
                                    encryptionContext: Mat.EncryptionContext,
                                    edks: seq<Mat.EncryptedDataKey>)
            returns (res: Option<seq<uint8>>)
            requires Valid()
            requires keyring.Valid()
            ensures Valid()
            ensures |edks| == 0 ==> res.None?
            ensures res.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(res.get)
        {
            if |edks| == 0 {
              return None;
            }
            var y := keyring.OnDecrypt(algorithmSuiteID, encryptionContext, edks);
            return match y {
                case Success(plaintextDataKey) => plaintextDataKey
                // TODO-RS: If all keyrings fail, pass on at least one of the errors,
                // preferrably all of them in a chain of some kind.
                case Failure(_) => None
            };
        }
    }
}
