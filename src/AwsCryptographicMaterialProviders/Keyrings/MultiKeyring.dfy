// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.MultiKeyring"}
  MaterialProviders.MultiKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import Aws.Crypto
  import Keyring
  import Materials
  import UTF8
  import Seq

  class MultiKeyring
    extends
    Keyring.VerifiableInterface,
    Crypto.IKeyring
  {
    // TODO: Make this an Option<Crypto.IKeyring> once supported
    // https://github.com/dafny-lang/dafny/issues/1499
    const generatorKeyring: Crypto.IKeyring?
    const childKeyrings: seq<Crypto.IKeyring>

    constructor (
      generatorKeyring: Crypto.IKeyring?,
      childKeyrings: seq<Crypto.IKeyring>
    )
      //= compliance/framework/multi-keyring.txt#2.6
      //= type=implication
      //# On keyring initialization, a keyring MUST define at least one of the
      //# following:
      requires generatorKeyring != null || |childKeyrings| > 0

      //= compliance/framework/multi-keyring.txt#2.6.1
      //= type=implication
      //# If the list of child keyrings (Section 2.6.2) is empty, a generator
      //# keyring (Section 2.6.1) MUST be defined for the keyring.
      requires |childKeyrings| == 0 ==> generatorKeyring != null

      //= compliance/framework/multi-keyring.txt#2.6.2
      //= type=implication
      //# If this keyring does not have a generator keyring (Section 2.6.1),
      //# this list MUST NOT be empty.
      requires generatorKeyring == null ==> |childKeyrings| > 0

      ensures this.generatorKeyring == generatorKeyring
      ensures this.childKeyrings == childKeyrings
    {
      this.generatorKeyring := generatorKeyring;
      this.childKeyrings := childKeyrings;
    }


    //= compliance/framework/multi-keyring.txt#2.6.1
    //= type=implication
    //# This keyring MUST implement the Generate Data Key (keyring-
    //# interface.md#generate-data-key) behavior during OnEncrypt (keyring-
    //# interface.md#onencrypt).
    method OnEncrypt(input: Crypto.OnEncryptInput)
      returns (res: Result<Crypto.OnEncryptOutput, string>)

      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      ensures res.Success? ==>
        //= compliance/framework/multi-keyring.txt#2.6.1
        //= type=implication
        //# This means that this keyring MUST return
        //# encryption materials (structures.md#encryption-materials) containing
        //# a plaintext data key on OnEncrypt (keyring-interface.md#onencrypt).
        && res.value.materials.plaintextDataKey.Some?
      
      //= compliance/framework/multi-keyring.txt#2.7.1
      //= type=implication
      //# If this keyring does not have a generator keyring (Section 2.6.1),
      //# and the input encryption materials (structures.md#encryption-
      //# materials) does not include a plaintext data key, OnEncrypt MUST
      //# fail.
      ensures this.generatorKeyring == null && input.materials.plaintextDataKey.None? ==> res.Failure?

      //= compliance/framework/multi-keyring.txt#2.7.1
      //= type=implication
      //# *  If the input encryption materials already include a plaintext data
      //# key, OnEncrypt MUST fail.
      ensures this.generatorKeyring != null && input.materials.plaintextDataKey.Some? ==> res.Failure?
    {

      // We could also frame this as "Need", but I found an "if" statement more clearly matches the 
      // requirement in the spec ("If this keyring does not have a generator keyring 
      //# and the input encryption materials does not include a plaintext data key")
      if this.generatorKeyring == null && input.materials.plaintextDataKey.None? {
          return Failure("Need either a generator keyring or input encryption materials which contain a plaintext data key");
      }

      var returnMaterials := input.materials;

      //= compliance/framework/multi-keyring.txt#2.7.1
      //# If this keyring has a generator keyring, this keyring MUST first
      //# generate a plaintext data key using the generator keyring:
      if this.generatorKeyring != null {

        :- Need(input.materials.plaintextDataKey.None?,
            "This multi keyring has a generator but provided Encryption Materials already contain plaintext data key");

        //= compliance/framework/multi-keyring.txt#2.7.1
        //# *  This keyring MUST first call the generator keyring's OnEncrypt
        //# using the input encryption materials as input.
        var onEncryptOutput := this.generatorKeyring.OnEncrypt(input);

        //= compliance/framework/multi-keyring.txt#2.7.1
        //# *  If the generator keyring fails OnEncrypt, this OnEncrypt MUST also
        //# fail.
        :- Need(onEncryptOutput.Success?, "Generator keyring failed to generate plaintext data key");

        //= compliance/framework/multi-keyring.txt#2.7.1
        //# *  If the generator keyring returns encryption materials missing a
        //# plaintext data key, OnEncrypt MUST fail.
        :- Need(Materials.EncryptionMaterialsTransitionIsValid(input.materials, onEncryptOutput.value.materials),
            "Generator keyring returned invalid encryption materials");

        returnMaterials := onEncryptOutput.value.materials;
      }

      for i := 0 to |this.childKeyrings|
        invariant returnMaterials.plaintextDataKey.Some?
      {
        var onEncryptInput := Crypto.OnEncryptInput(materials := returnMaterials);

        //= compliance/framework/multi-keyring.txt#2.7.1
        //# Next, for each keyring (keyring-interface.md) in this keyring's list
        //# of child keyrings (Section 2.6.2), the keyring MUST call OnEncrypt
        //# (keyring-interface.md#onencrypt).
        var onEncryptOutput := this.childKeyrings[i].OnEncrypt(onEncryptInput);

        //= compliance/framework/multi-keyring.txt#2.7.1
        //# If the child keyring's OnEncrypt (keyring-
        //# interface.md#onencrypt) fails, this OnEncrypt MUST also fail.
        :- Need(onEncryptOutput.Success?, "Child keyring failed to encrypt plaintext data key");

        // We have to explicitly check for this because our child and generator keyrings are of type
        // IKeyring, rather than VerifiableKeyring. If we knew we would always have VerifiableKeyrings,
        // we would get this for free. However, we want to support customer implementations of keyrings
        // which may or may not perform valid transitions.
        :- Need(Materials.EncryptionMaterialsTransitionIsValid(returnMaterials, onEncryptOutput.value.materials),
            "Child keyring performed invalid transition on encryption materials");

        returnMaterials := onEncryptOutput.value.materials;
      }

      if !Materials.EncryptionMaterialsTransitionIsValid(input.materials, returnMaterials) {
       return Failure("A child or generator keyring modified the encryption materials in illegal ways.");
      }

      //= compliance/framework/multi-keyring.txt#2.7.1
      //# If all previous OnEncrypt (keyring-interface.md#onencrypt) calls
      //# succeeded, this keyring MUST return the encryption materials
      //# (structures.md#encryption-materials) returned by the last OnEncrypt
      //# call.
      return Success(Crypto.OnEncryptOutput(materials := returnMaterials));
    }

    /*
     * OnDecrypt
     */
    method OnDecrypt(input: Crypto.OnDecryptInput)
      returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      //= compliance/framework/multi-keyring.txt#2.7.2
      //= type=implication
      //# If the decryption materials already contain a plaintext data key, the
      //# keyring MUST fail and MUST NOT modify the decryption materials
      //# (structures.md#decryption-materials).      
      ensures Materials.DecryptionMaterialsWithPlaintextDataKey(input.materials) ==> res.Failure?

      // TODO/QQ: how to check "does not modify input materials"?
    {
      // We won't actually be returning these materials, but it's useful to have a reference to them
      // for proving things (for example, proving we never enter a state where we get a plaintext data
      // key from a child keyring and DON'T return it)
      var materials := input.materials;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(input.materials),
        "Keyring received decryption materials that already contain a plaintext data key.");

      // Failure messages will be collected here
      var failures : seq<string> := [];


      //= compliance/framework/multi-keyring.txt#2.7.2
      //# Otherwise, OnDecrypt MUST first attempt to decrypt the encrypted data
      //# keys (structures.md#encrypted-data-keys-1) in the input decryption
      //# materials (structures.md#decryption-materials) using its generator
      //# keyring (Section 2.6.1).
      if this.generatorKeyring != null {

        var result := AttemptDecryptDataKey(this.generatorKeyring, input);

        if result.Success? {
          if result.value.materials.plaintextDataKey.Some? {
            return result;
          }
        } else {
          failures := failures + [result.error];
        }
      }

      //= compliance/framework/multi-keyring.txt#2.7.2
      //# If the generator keyring is unable to
      //# decrypt the materials, the multi-keyring MUST attempt to decrypt
      //# using its child keyrings.
      for j := 0 to |this.childKeyrings|
        invariant Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials)
      {

        //= compliance/framework/multi-keyring.txt#2.7.2
        //# For each keyring (keyring-interface.md) to be used for decryption,
        //# the multi-keyring MUST call that keyring's OnDecrypt (keyring-
        //# interface.md#ondecrypt) using the unmodified decryption materials
        //# (structures.md#decryption-materials) and the input encrypted data key
        //# (structures.md#encrypted-data-key) list.
        var result := AttemptDecryptDataKey(this.childKeyrings[j], input);

        if result.Success? {
          materials := result.value.materials;
          //= compliance/framework/multi-keyring.txt#2.7.2
          //# If OnDecrypt (keyring-
          //# interface.md#ondecrypt) returns decryption materials
          //# (structures.md#decryption-materials) containing a plaintext data key,
          //# the multi-keyring MUST immediately return the modified decryption
          //# materials.
          if materials.plaintextDataKey.Some? {
            return Success(result.value);
          }
        } else {
          //= compliance/framework/multi-keyring.txt#2.7.2
          //# If the child keyring's OnDecrypt call fails, the multi-
          //# keyring MUST collect the error and continue to the next keyring, if
          //# any.
          failures := failures + [result.error];
        }
      }

      if materials.plaintextDataKey.None? {

        //= compliance/framework/multi-keyring.txt#2.7.2
        //# If, after calling OnDecrypt (keyring-interface.md#ondecrypt) on every
        //# child keyring (Section 2.6.2) (and possibly the generator keyring
        //# (Section 2.6.1)), the decryption materials (structures.md#decryption-
        //# materials) still do not contain a plaintext data key, OnDecrypt MUST
        //# return a failure message containing the collected failure messages
        //# from the child keyrings.
        var concatString := (s, a) => a + "\n" + s;
        var error := Seq.FoldRight(
          concatString,
          failures,
          "Unable to decrypt data key:\n"
        );
        return Failure(error);
      }
    }
  }

  method AttemptDecryptDataKey(keyring: Crypto.IKeyring, input: Crypto.OnDecryptInput)
    returns (res: Result<Crypto.OnDecryptOutput, string>)
    ensures res.Success?
      ==> && res.value.materials.plaintextDataKey.Some?
          && Materials.DecryptionMaterialsTransitionIsValid(input.materials, res.value.materials)
    {
      var output :- keyring.OnDecrypt(input);

      if output.materials.plaintextDataKey.Some? {
        if !Materials.DecryptionMaterialsTransitionIsValid(input.materials, output.materials) {
          return Failure("Keyring performed invalid material transition");
        }   
        return Success(output);
      } else {
        return Failure("Could not decrypt data key");
      }
  }
}
