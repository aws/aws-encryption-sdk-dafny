// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "TestUtils.dfy"
include "../src/KeyWrapping/IntermediateKeyWrapping.dfy"

module TestIntermediateKeyWrapping {
  import Types = AwsCryptographyMaterialProvidersTypes
  import MaterialProviders
  import opened TestUtils
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import opened Actions
  import opened IntermediateKeyWrapping
  import MaterialWrapping
  import AlgorithmSuites

  const TEST_ALG_SUITE := AlgorithmSuites.DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384;
  const PLAINTEXT_MAT : seq<uint8> := seq(TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int, _ => 1);
  const WRAPPED_MAT : seq<uint8> := seq(TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int, _ => 2);

  method {:test} IntermediateWrapUnwrapTest() {
    var encCtx := map[];
    var keyLen := TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int;
    var tagLen := TEST_ALG_SUITE.encrypt.AES_GCM.tagLength as int;
    var pdk: seq<uint8> := seq(keyLen, _ => 0);

    var testGenerateAndWrap := new TestGenerateAndWrapKeyMaterial();
    var intermediateWrapOutput := IntermediateWrap(
        testGenerateAndWrap,
        pdk,
        TEST_ALG_SUITE,
        encCtx
    );
    expect intermediateWrapOutput.Success?;
    expect |intermediateWrapOutput.value.wrappedMaterial| == keyLen + tagLen + |WRAPPED_MAT|;
    expect intermediateWrapOutput.value.wrappedMaterial[keyLen+tagLen..] == WRAPPED_MAT;

    var testUnwrap := new TestUnwrapKeyMaterial();
    var intermediateUnwrapOutput := IntermediateUnwrap(
        testUnwrap,
        intermediateWrapOutput.value.wrappedMaterial,
        TEST_ALG_SUITE,
        encCtx
    );
    expect intermediateUnwrapOutput.Success?;
    expect intermediateUnwrapOutput.value.plaintextDataKey == pdk;
    expect intermediateWrapOutput.value.symmetricSigningKey == intermediateUnwrapOutput.value.symmetricSigningKey;
  }

  method {:test} IntermediateGenerateAndWrapUnwrapTest() {
    var encCtx := map[];
    var keyLen := TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int;
    var tagLen := TEST_ALG_SUITE.encrypt.AES_GCM.tagLength as int;

    var testGenerateAndWrap := new TestGenerateAndWrapKeyMaterial();
    var intermediateWrapOutput := IntermediateGenerateAndWrap(
        testGenerateAndWrap,
        TEST_ALG_SUITE,
        encCtx
    );
    expect intermediateWrapOutput.Success?;
    expect |intermediateWrapOutput.value.wrappedMaterial| == keyLen + tagLen + |WRAPPED_MAT|;
    expect intermediateWrapOutput.value.wrappedMaterial[keyLen+tagLen..] == WRAPPED_MAT;

    var testUnwrap := new TestUnwrapKeyMaterial();
    var intermediateUnwrapOutput := IntermediateUnwrap(
        testUnwrap,
        intermediateWrapOutput.value.wrappedMaterial,
        TEST_ALG_SUITE,
        encCtx
    );
    expect intermediateUnwrapOutput.Success?;
    expect intermediateWrapOutput.value.plaintextDataKey == intermediateUnwrapOutput.value.plaintextDataKey;
    expect intermediateWrapOutput.value.symmetricSigningKey == intermediateUnwrapOutput.value.symmetricSigningKey;
  }

  datatype TestInfo = TestInfo()

  class TestGenerateAndWrapKeyMaterial
    extends MaterialWrapping.GenerateAndWrapMaterial<TestInfo>
  {
    constructor()
      ensures Invariant()
    {
      Modifies := {};
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      Modifies == {}
    }

    predicate Ensures(
      input: MaterialWrapping.GenerateAndWrapInput,
      res: Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {true}

    method Invoke(
      input: MaterialWrapping.GenerateAndWrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.plaintextMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      :- Need(input.algorithmSuite == TEST_ALG_SUITE,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unexpected input on TestGenerateAndWrapMaterial"));
      return Success(MaterialWrapping.GenerateAndWrapOutput(
        plaintextMaterial := PLAINTEXT_MAT,
        wrappedMaterial := WRAPPED_MAT,
        wrapInfo := TestInfo()
      ));
    }
  }

  class TestUnwrapKeyMaterial
    extends MaterialWrapping.UnwrapMaterial<TestInfo>
  {
    constructor()
      ensures Invariant()
    {
      Modifies := {};
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      Modifies == {}
    }

    predicate Ensures(
      input: MaterialWrapping.UnwrapInput,
      res: Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {true}

    method Invoke(
      input: MaterialWrapping.UnwrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      :- Need(input.wrappedMaterial == WRAPPED_MAT,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unexpected input on TestUnwrapMaterial"));
      :- Need(input.algorithmSuite == TEST_ALG_SUITE,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unexpected input on TestUnwrapMaterial"));
      return Success(MaterialWrapping.UnwrapOutput(
        unwrappedMaterial := PLAINTEXT_MAT,
        unwrapInfo := TestInfo()
      ));
    }
  }
}
