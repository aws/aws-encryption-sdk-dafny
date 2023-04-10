// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/Index.dfy"
include "../TestUtils.dfy"

module TestMultiKeyring {
  import opened Wrappers
  import TestUtils
  import UTF8
  import Aws.Cryptography.Primitives
  import AwsCryptographyPrimitivesTypes
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes

  method getInputEncryptionMaterials(encryptionContext: Types.EncryptionContext) returns (res: Types.EncryptionMaterials) {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None,
        requiredEncryptionContextKeys := []
      )
    );
    return encryptionMaterialsIn;
  }

  method getInputDecryptionMaterials(encryptionContext: Types.EncryptionContext) returns (res: Types.DecryptionMaterials) {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := []
      )
    );
    return decryptionMaterialsIn;
  }

  method {:test} TestHappyCase()
  {
    
    var mpl :- expect MaterialProviders.MaterialProviders();

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var decryptionMaterials := getInputDecryptionMaterials(encryptionContext);

    // To confirm that the multi-keyring is generating the plaintext data key using the generator, we'll
    // directly get materials using the generator
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var expectedEncryptionMaterials := rawAESKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterials)
    );
    expect expectedEncryptionMaterials.Success?;
    var expectedPlaintextDataKey := expectedEncryptionMaterials.value.materials.plaintextDataKey;
    expect expectedPlaintextDataKey.Some?;

    var staticKeyring := SetupStaticKeyring(Some(expectedEncryptionMaterials.value.materials), None());

    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(staticKeyring),
        childKeyrings := [rawAESKeyring]
    ));

    var encryptionMaterialsOut :- expect multiKeyring.OnEncrypt(Types.OnEncryptInput(materials:=encryptionMaterials));

    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# If this keyring has a generator keyring, this keyring MUST first
    //# generate a plaintext data key using the generator keyring:

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# *  This keyring MUST first call the generator keyring's OnEncrypt
    //# using the input encryption materials as input.
    expect encryptionMaterialsOut.materials.plaintextDataKey.value == expectedPlaintextDataKey.value;

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# Next, for each keyring (keyring-interface.md) in this keyring's list
    //# of child keyrings (Section 2.6.2), the keyring MUST call OnEncrypt
    //# (keyring-interface.md#onencrypt).

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# If all previous OnEncrypt (keyring-interface.md#onencrypt) calls
    //# succeeded, this keyring MUST return the encryption materials
    //# (structures.md#encryption-materials) returned by the last OnEncrypt
    //# call.
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 2;
  }

  method {:test} TestChildKeyringFailureEncrypt() {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# If the child keyring's OnEncrypt (keyring-
    //# interface.md#onencrypt) fails, this OnEncrypt MUST also fail.
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var failingKeyring := SetupFailingKeyring();

    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(rawAESKeyring),
        childKeyrings := [failingKeyring]
    ));

    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);

    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials:=encryptionMaterials));
    expect result.IsFailure();
  }

  method {:test} TestGeneratorKeyringFails() {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# *  If the generator keyring fails OnEncrypt, this OnEncrypt MUST also
    //# fail.
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var failingKeyring := SetupFailingKeyring();

    // We'll add a functional AES keyring as a small validation that something *could* have succeeded in
    // generating but the call still fails.
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);

    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(failingKeyring),
        childKeyrings := [rawAESKeyring]
    ));

    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);

    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials:=encryptionMaterials));
    expect result.IsFailure();
  }

  method {:test} TestGeneratorKeyringDoesNotReturnPlaintextDataKey() {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.1
    //= type=test
    //# *  If the generator keyring returns encryption materials missing a
    //# plaintext data key, OnEncrypt MUST fail.
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var failingKeyring := SetupStaticKeyring(Some(encryptionMaterials), None());

    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(failingKeyring),
        childKeyrings := []
    ));

    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials:=encryptionMaterials));
    expect result.IsFailure();
  }

  method {:test} TestGeneratorAbleToDecrypt() {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=test
    //# Otherwise, OnDecrypt MUST first attempt to decrypt the encrypted data
    //# keys (structures.md#encrypted-data-keys-1) in the input decryption
    //# materials (structures.md#decryption-materials) using its generator
    //# keyring (Section 2.6.1).

    // Generate some materials to decrypt
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var inputEncryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var encryptionMaterials := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials:=inputEncryptionMaterials));
    expect encryptionMaterials.Success?;

    var inputDecryptionMaterials := getInputDecryptionMaterials(encryptionContext);

    var failingKeyring := SetupFailingKeyring();

    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(rawAESKeyring),
        childKeyrings := [failingKeyring]
    ));

    var onDecryptInput := Types.OnDecryptInput(
      materials := inputDecryptionMaterials, encryptedDataKeys := encryptionMaterials.value.materials.encryptedDataKeys
    );

    var decryptionMaterials := multiKeyring.OnDecrypt(input:=onDecryptInput);
    expect decryptionMaterials.Success?;
    expect decryptionMaterials.value.materials.plaintextDataKey == encryptionMaterials.value.materials.plaintextDataKey;
  }

  method {:test} TestGeneratorUnableToDecrypt() {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=test
    //# If the generator keyring is unable to
    //# decrypt the materials, the multi-keyring MUST attempt to decrypt
    //# using its child keyrings, until one either succeeds in decryption or
    //# all have failed.

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=TODO
    //# For each keyring (keyring-interface.md) to be used for decryption,
    //# the multi-keyring MUST call that keyring's OnDecrypt (keyring-
    //# interface.md#ondecrypt) using the unmodified decryption materials
    //# (structures.md#decryption-materials) and the input encrypted data key
    //# (structures.md#encrypted-data-key) list.
    // Marked as TODO because we don't yet have a way of confirming the exact
    // parameters passed to child keyrings. Investigate our "spy" patterns at
    // some point

    // Generate some materials to decrypt
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var inputEncryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var encryptionMaterials := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials:=inputEncryptionMaterials));
    expect encryptionMaterials.Success?;

    var inputDecryptionMaterials := getInputDecryptionMaterials(encryptionContext);

    var failingKeyring := SetupFailingKeyring();

    // For children, we add failing keyrings on both sides of the valid keyring so we exercise
    // all paths
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := Some(failingKeyring),
        childKeyrings := [failingKeyring, rawAESKeyring, failingKeyring]
    ));

    var onDecryptInput := Types.OnDecryptInput(
      materials := inputDecryptionMaterials, encryptedDataKeys := encryptionMaterials.value.materials.encryptedDataKeys
    );

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=TODO
    //# If OnDecrypt (keyring-
    //# interface.md#ondecrypt) returns decryption materials
    //# (structures.md#decryption-materials) containing a plaintext data key,
    //# the multi-keyring MUST immediately return the modified decryption
    //# materials.
    // Marked as TODO because we don't yet have a way of confirming the "immediately"
    // requirement. We ensure we got the right output, but we don't ensure we didn't try
    // the other keyrings before returning. Look into the "spy" pattern at some point
    var decryptionMaterials := multiKeyring.OnDecrypt(input:=onDecryptInput);
    expect decryptionMaterials.Success?;
    expect decryptionMaterials.value.materials.plaintextDataKey == encryptionMaterials.value.materials.plaintextDataKey;
  }

  method {:test} TestCollectFailuresDecrypt()
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=test
    //# If the child keyring's OnDecrypt call fails, the multi-
    //# keyring MUST collect the error and continue to the next keyring, if
    //# any.

    //= compliance/framework/multi-keyring.txt#2.7.2
    //= type=test
    //# If, after calling OnDecrypt (keyring-interface.md#ondecrypt) on every
    //# child keyring (Section 2.6.2) (and possibly the generator keyring
    //# (Section 2.6.1)), the decryption materials (structures.md#decryption-
    //# materials) still do not contain a plaintext data key, OnDecrypt MUST
    //# return a failure message containing the collected failure messages
    //# from the child keyrings.
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var failingKeyring := SetupFailingKeyring();
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(
        generator := None(),
        childKeyrings := [failingKeyring, failingKeyring]
    ));

    var materials :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF),
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := []
      )
    );

    var result := multiKeyring.OnDecrypt(Types.OnDecryptInput(materials:=materials, encryptedDataKeys:=[]));
    expect result.IsFailure();
  }

  method setupRawAesKeyring(encryptionContext: Types.EncryptionContext)
    returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
    ));
    return rawAESKeyring;
  }
  
  method SetupStaticKeyring(
      encryptionMaterials: Option<Types.EncryptionMaterials>,
      decryptionMaterials: Option<Types.DecryptionMaterials>
    ) returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
  {
    return new StaticKeyring(encryptionMaterials, decryptionMaterials);
  }

  method SetupFailingKeyring() returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
  {
    return new FailingKeyring();
  }

  /*
   * A keyring which always returns a specific static set of materials. Used for testing.
   */
  class StaticKeyring extends Types.IKeyring {
    const encryptionMaterials: Option<Types.EncryptionMaterials>;
    const decryptionMaterials: Option<Types.DecryptionMaterials>;

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>) {true}
    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>){true}

    constructor(
      encryptionMaterials: Option<Types.EncryptionMaterials>,
      decryptionMaterials: Option<Types.DecryptionMaterials>
    )
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      this.encryptionMaterials := encryptionMaterials;
      this.decryptionMaterials := decryptionMaterials;
      History := new Types.IKeyringCallHistory();
      Modifies := { History };
    }

    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
    {
      if this.encryptionMaterials.Some? {
        return Success(Types.OnEncryptOutput(materials:=encryptionMaterials.value));
      } else {
        var exception := Types.AwsCryptographicMaterialProvidersException(message := "Failure");
        return Failure(exception);
      }
    }

    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
    {
      if this.decryptionMaterials.Some? {
        return Success(Types.OnDecryptOutput(materials:=decryptionMaterials.value));
      } else {
        var exception := Types.AwsCryptographicMaterialProvidersException(message := "Failure");
        return Failure(exception);
      }
    }
  }

  /*
   * Keyring that fails all calls. Used for testing
   */
  class FailingKeyring extends Types.IKeyring {

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>) {true}
    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>){true}

    constructor()
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      History := new Types.IKeyringCallHistory();
      Modifies := { History };
    }

    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      
    {
      var exception := Types.AwsCryptographicMaterialProvidersException(message := "Failure");
      return Failure(exception);
    }

    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
    {
      var exception := Types.AwsCryptographicMaterialProvidersException(message := "Failure");
      return Failure(exception);
    }
  }
}
