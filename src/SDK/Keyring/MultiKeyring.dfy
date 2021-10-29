// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Random.dfy"
include "../Materials.dfy"

module {:extern "MultiKeyringDef"} MultiKeyringDef {
    import opened KeyringDefs
    import opened Wrappers
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
            ensures Valid() && fresh(Repr - (if g != null then g.Repr else {}) - childrenRepr(c))
            ensures
                && generator == g
                && children == c
        {
            generator := g;
            children := c;
            Repr := {this} + (if g != null then g.Repr else {}) + childrenRepr(c);
        }

        predicate Valid()
          reads this, Repr
          ensures Valid() ==> this in Repr
        {
            && this in Repr
            && (generator != null ==> generator in Repr && generator.Repr <= Repr && generator.Valid())
            && (forall j :: 0 <= j < |children| ==> children[j] in Repr && children[j].Repr <= Repr && children[j].Valid())
        }

        method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
            requires Valid()
            ensures Valid()
            ensures OnEncryptPure(materials, res)
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
                         edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
            requires Valid()
            ensures Valid()
            ensures OnDecryptPure(materials, res)
        {
            if materials.plaintextDataKey.Some? {
                return Success(materials);
            }
            if generator != null {
                var onDecryptResult := generator.OnDecrypt(materials, edks);
                if onDecryptResult.Success? {
                    return onDecryptResult;
                }
            }
            var i := 0;
            res := Success(materials);
            while i < |children|
                invariant res.Success? ==>
                        && materials.encryptionContext == res.value.encryptionContext
                        && materials.algorithmSuiteID == res.value.algorithmSuiteID
                        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
                        && materials.verificationKey == res.value.verificationKey
                decreases |children| - i
            {
                var onDecryptResult := children[i].OnDecrypt(materials, edks);
                if onDecryptResult.Success? {
                    return onDecryptResult;
                }
                i := i + 1;
            }
            return Failure("Unable to decrypt.");
        }
    }
}
