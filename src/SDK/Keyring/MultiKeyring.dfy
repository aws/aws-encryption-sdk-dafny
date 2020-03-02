include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Random.dfy"
include "../Materials.dfy"

module {:extern "MultiKeyringDef"} MultiKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import AlgorithmSuite
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
        const children : seq<Keyring>
        constructor (g : Keyring?, c : seq<Keyring>) ensures generator == g ensures children == c
            requires g != null ==> g.Valid()
            requires forall i :: 0 <= i < |c| ==> c[i].Valid()
            ensures Valid()
        {
            generator := g;
            children := c;
            Repr := {this} + (if g != null then {g} + g.Repr else {}) + childrenRepr(c);
        }

        predicate Valid() {
            && (generator != null ==> generator in Repr && generator.Repr <= Repr && generator.Valid())
            && (forall j :: 0 <= j < |children| ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid())
        }

        method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
            requires Valid()
            ensures Valid()
            ensures res.Success? ==> 
                    && materials.encryptionContext == res.value.encryptionContext
                    && materials.algorithmSuiteID == res.value.algorithmSuiteID 
                    && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
                    && materials.keyringTrace <= res.value.keyringTrace
                    && materials.encryptedDataKeys <= res.value.encryptedDataKeys
                    && materials.signingKey == res.value.signingKey
            // TODO-RS: Temporary to let everything compile, hoping to not have to do this permanently.
            decreases *
        {
            // First pass on or generate the plaintext data key
            var resultMaterials := materials;
            if generator != null {
                resultMaterials :- generator.OnEncrypt(resultMaterials);
            }
            if resultMaterials.plaintextDataKey.None? {
                return Failure("Bad state: data key not found");
            }

            // Then apply each of the children in sequence
            // TODO-RS: Use folding here instead
            var i := 0;
            while i < |children|
                invariant resultMaterials.plaintextDataKey.Some?
                invariant materials.encryptionContext == resultMaterials.encryptionContext
                invariant materials.algorithmSuiteID == resultMaterials.algorithmSuiteID
                invariant materials.plaintextDataKey.Some? ==> resultMaterials.plaintextDataKey == materials.plaintextDataKey
                invariant materials.keyringTrace <= resultMaterials.keyringTrace
                invariant materials.encryptedDataKeys <= resultMaterials.encryptedDataKeys
                invariant materials.signingKey == resultMaterials.signingKey
                decreases |children| - i 
            {
                resultMaterials :- children[i].OnEncrypt(resultMaterials);
                i := i + 1;
            }
            res := Success(resultMaterials);
        }
        method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                         edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
            requires Valid()
            ensures Valid()
            ensures |edks| == 0 ==> res.Success? && materials == res.value
            ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
            ensures res.Success? ==>
                && materials.encryptionContext == res.value.encryptionContext
                && materials.algorithmSuiteID == res.value.algorithmSuiteID
                && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
                && materials.keyringTrace <= res.value.keyringTrace
                && materials.verificationKey == res.value.verificationKey
            // TODO-RS: Temporary to let everything compile, hoping to not have to do this permanently.
            decreases *
        {
            res := Success(materials);
            if |edks| == 0 || materials.plaintextDataKey.Some? {
                return res;
            }
            if generator != null {
                var onDecryptResult := generator.OnDecrypt(materials, edks);
                if onDecryptResult.Failure? {
                    res := onDecryptResult;
                } else if onDecryptResult.value.plaintextDataKey.Some? {
                    return onDecryptResult;
                }
            }
            var i := 0;
            while i < |children|
                invariant res.Success? ==> 
                        && materials.encryptionContext == res.value.encryptionContext
                        && materials.algorithmSuiteID == res.value.algorithmSuiteID 
                        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
                        && materials.keyringTrace <= res.value.keyringTrace
                        && materials.verificationKey == res.value.verificationKey
                decreases |children| - i
            {
                var onDecryptResult := children[i].OnDecrypt(materials, edks);
                if onDecryptResult.Failure? {
                    res := onDecryptResult;
                } else if onDecryptResult.value.plaintextDataKey.Some? {
                    return onDecryptResult;
                }
                i := i + 1;
            }
            return res;
        }
    }
}
