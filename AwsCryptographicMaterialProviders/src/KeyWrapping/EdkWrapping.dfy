// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../Materials.dfy"
include "MaterialWrapping.dfy"
include "IntermediateKeyWrapping.dfy"

// Helpers for implementing EDK wrapping according to the
// EDK Wrapping Algorithm in the Algorithm Suite.
// Keyrings can make use of these helpers by extending the
// traits in MaterialWrapping.dfy to encapsulate how that keyring Generates/Wraps/Unwraps
// raw key material.
module EdkWrapping {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Actions
  import opened Wrappers
  import opened MaterialWrapping
  import opened IntermediateKeyWrapping
  import Crypto = AwsCryptographyPrimitivesTypes
  import Types = AwsCryptographyMaterialProvidersTypes
  import Aws.Cryptography.Primitives
  import Materials
  import AlgorithmSuites

  datatype WrapEdkMaterialOutput<T> =
    | WrapOnlyEdkMaterialOutput(
      // SHOULD be included in the EDK ciphertext
      nameonly wrappedMaterial: seq<uint8>,
      // SHOULD be used for the symmetric signing key
      nameonly symmetricSigningKey: Option<Types.Secret>,
      // MAY be utilized to pass additional information from the wrap operation
      // to be used in EDK creation or the update to the encryption materials
      nameonly wrapInfo: T,
      // Important for ensuring various properties of these helpers within this module.
      nameonly ghost intermediateMaterial: Option<seq<uint8>>)
    | GenerateAndWrapEdkMaterialOutput(
      // SHOULD be used for the plaintext data key
      nameonly plaintextDataKey: seq<uint8>,
      // SHOULD be included in the EDK ciphertext
      nameonly wrappedMaterial: seq<uint8>,
      // SHOULD be used for the symmetric signing key
      nameonly symmetricSigningKey: Option<Types.Secret>,
      // MAY be utilized to pass additional information from the generateAndWrap operation
      // to be used in EDK creation or the update to the encryption materials
      nameonly wrapInfo: T,
      // Important for ensuring various properties of these helpers within this module.
      nameonly ghost intermediateMaterial: Option<seq<uint8>>)

  datatype UnwrapEdkMaterialOutput<T> = UnwrapEdkMaterialOutput(
    // SHOULD be used as the plaintext data key
    nameonly plaintextDataKey: seq<uint8>,
    // SHOULD be used as the symmetric signing key
    nameonly symmetricSigningKey: Option<Types.Secret>,
    // MAY be utilized to pass additional information from the unwrap operation
    // to be used in the update to the decryption materials
    nameonly unwrapInfo: T,
    // Important for ensuring various properties of these helpers within this module.
    nameonly ghost intermediateMaterial: Option<seq<uint8>>
  )

  // Given encryption materials,
  // either return a new pdk with it's wrapped form and associated materials,
  // or return a wrapped form of the existing pdk and associated materials.
  // This method will wrap the pdk according to the Edk Wrapping Algorithm
  // indicated in the algorithm suite.
  // The keyring can then use the returned information to serialize
  // the Edk and populate the encryption materials appropriately.
  // Generic type T can be utilized to pass information from the wrapping procedure
  // back to the caller.
  method WrapEdkMaterial<T>(
    nameonly encryptionMaterials: Types.EncryptionMaterials,
    nameonly wrap: MaterialWrapping.WrapMaterial<T>,
    nameonly generateAndWrap: MaterialWrapping.GenerateAndWrapMaterial<T>
  ) returns (ret: Result<WrapEdkMaterialOutput<T>, Types.Error>)
    requires wrap.Invariant()
    requires generateAndWrap.Invariant()
    modifies wrap.Modifies + generateAndWrap.Modifies

    //////////
    // Specify behavior for wrapping existing pdk with DIRECT_KEY_WRAPPING via wrap.
    ensures
        && ret.Success?
        && encryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
        && encryptionMaterials.plaintextDataKey.Some?
      ==>
        && ret.value.WrapOnlyEdkMaterialOutput?
        && var wrapRes := WrapOutput(
          wrappedMaterial := ret.value.wrappedMaterial,
          wrapInfo := ret.value.wrapInfo);
        && wrap.Ensures(
          WrapInput(
            plaintextMaterial := encryptionMaterials.plaintextDataKey.value,
            algorithmSuite := encryptionMaterials.algorithmSuite,
            encryptionContext := encryptionMaterials.encryptionContext),
          Success(wrapRes),
          [])

    //////////
    // Specify behavior for wrapping existing pdk with IntermediateKeyWrapping via generateAndWrap.
    ensures
        && ret.Success?
        && encryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?
        && encryptionMaterials.plaintextDataKey.Some?
      ==>
        && ret.value.WrapOnlyEdkMaterialOutput?
        && ret.value.intermediateMaterial.Some?
        && var encryptedPdkLen :=
          (AlgorithmSuites.GetEncryptKeyLength(encryptionMaterials.algorithmSuite)
            + AlgorithmSuites.GetEncryptTagLength(encryptionMaterials.algorithmSuite)) as nat;
        && |ret.value.wrappedMaterial| >= encryptedPdkLen
        && generateAndWrap.Ensures(
          MaterialWrapping.GenerateAndWrapInput(
            algorithmSuite := encryptionMaterials.algorithmSuite,
            encryptionContext := encryptionMaterials.encryptionContext),
          Success(
            MaterialWrapping.GenerateAndWrapOutput(
              plaintextMaterial := ret.value.intermediateMaterial.value,
              // Here we prove we return the material from generateAndWrap,
              // which is appended to the encryptedPdk during Intermediate Key Wrapping
              wrappedMaterial := ret.value.wrappedMaterial[encryptedPdkLen..],
              wrapInfo := ret.value.wrapInfo)),
          [])

    //////////
    // Specify behavior for creating new pdk and wrapping with DIRECT_KEY_WRAPPING via generateAndWrap.
    ensures
        && ret.Success?
        && encryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
        && encryptionMaterials.plaintextDataKey.None?
      ==>
        && ret.value.GenerateAndWrapEdkMaterialOutput?
        && var generateAndWrapRes := MaterialWrapping.GenerateAndWrapOutput(
          plaintextMaterial := ret.value.plaintextDataKey,
          wrappedMaterial := ret.value.wrappedMaterial,
          wrapInfo := ret.value.wrapInfo);
        && generateAndWrap.Ensures(
          MaterialWrapping.GenerateAndWrapInput(
            algorithmSuite := encryptionMaterials.algorithmSuite,
            encryptionContext := encryptionMaterials.encryptionContext),
          Success(generateAndWrapRes),
          [])
        && |ret.value.plaintextDataKey| == AlgorithmSuites.GetEncryptKeyLength(encryptionMaterials.algorithmSuite) as nat
    
    // Specify behavior for creating new pdk and wrapping with IntermediateKeyWrapping via generateAndWrap.
    ensures
        && ret.Success?
        && encryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?
        && encryptionMaterials.plaintextDataKey.None?
      ==>
        && ret.value.GenerateAndWrapEdkMaterialOutput?
        && ret.value.intermediateMaterial.Some?
        && var encryptedPdkLen :=
          (AlgorithmSuites.GetEncryptKeyLength(encryptionMaterials.algorithmSuite)
            + AlgorithmSuites.GetEncryptTagLength(encryptionMaterials.algorithmSuite)) as nat;
        && |ret.value.wrappedMaterial| >= encryptedPdkLen
        && generateAndWrap.Ensures(
          MaterialWrapping.GenerateAndWrapInput(
            algorithmSuite := encryptionMaterials.algorithmSuite,
            encryptionContext := encryptionMaterials.encryptionContext),
          Success(
            MaterialWrapping.GenerateAndWrapOutput(
              plaintextMaterial := ret.value.intermediateMaterial.value,
              // Here we prove we return the material from generateAndWrap,
              // which is appended to the encryptedPdk during Intermediate Key Wrapping
              wrappedMaterial := ret.value.wrappedMaterial[encryptedPdkLen..],
              wrapInfo := ret.value.wrapInfo)),
          [])
  {
    :- Need(Materials.ValidEncryptionMaterials(encryptionMaterials),
      Types.AwsCryptographicMaterialProvidersException(
        message := "Invalid materials for decryption."));

    if (encryptionMaterials.plaintextDataKey.Some? && 
        encryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?)  {
      // Wrap the pdk in the materials directly
      var directOutput :- wrap.Invoke(
        WrapInput(
          plaintextMaterial := encryptionMaterials.plaintextDataKey.value,
          algorithmSuite := encryptionMaterials.algorithmSuite,
          encryptionContext := encryptionMaterials.encryptionContext
        ), []);

      return Success(
        WrapOnlyEdkMaterialOutput(
          wrappedMaterial := directOutput.wrappedMaterial,
          symmetricSigningKey := None,
          wrapInfo := directOutput.wrapInfo,
          intermediateMaterial := None
        )
      );
    } else if (encryptionMaterials.plaintextDataKey.Some? && 
        encryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?) {
      // Wrap the pdk in the materials using Intermediate Key Wrapping

      var intermediateOutput :- IntermediateWrap(
        generateAndWrap := generateAndWrap,
        plaintextDataKey := encryptionMaterials.plaintextDataKey.value,
        algorithmSuite := encryptionMaterials.algorithmSuite,
        encryptionContext := encryptionMaterials.encryptionContext
      );

      return Success(
        WrapOnlyEdkMaterialOutput(
          wrappedMaterial := intermediateOutput.wrappedMaterial,
          symmetricSigningKey := Some(intermediateOutput.symmetricSigningKey),
          wrapInfo := intermediateOutput.wrapInfo,
          intermediateMaterial := Some(intermediateOutput.intermediateMaterial)
        )
      );
    } else if (encryptionMaterials.plaintextDataKey.None?
        && encryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?)  {
      // Generate pdk and wrap it directly
      var directOutput :- generateAndWrap.Invoke(
        MaterialWrapping.GenerateAndWrapInput(
          algorithmSuite := encryptionMaterials.algorithmSuite,
          encryptionContext := encryptionMaterials.encryptionContext
        ), []);

      return Success(
        GenerateAndWrapEdkMaterialOutput(
          plaintextDataKey := directOutput.plaintextMaterial,
          wrappedMaterial := directOutput.wrappedMaterial,
          symmetricSigningKey := None,
          wrapInfo := directOutput.wrapInfo,
          intermediateMaterial := None
        )
      );
    } else if (encryptionMaterials.plaintextDataKey.None?
        && encryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?) {
      // Generate pdk and wrap using Intermediate Key Wrapping
      :- Need(encryptionMaterials.algorithmSuite.commitment.HKDF?,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid algorithm suite: suites with intermediate key wrapping must use key commitment."));

      var intermediateOutput :- IntermediateGenerateAndWrap(
        generateAndWrap := generateAndWrap,
        algorithmSuite := encryptionMaterials.algorithmSuite,
        encryptionContext := encryptionMaterials.encryptionContext
      );

      return Success(
        GenerateAndWrapEdkMaterialOutput(
          plaintextDataKey := intermediateOutput.plaintextDataKey,
          wrappedMaterial := intermediateOutput.wrappedMaterial,
          symmetricSigningKey := Some(intermediateOutput.symmetricSigningKey),
          wrapInfo := intermediateOutput.wrapInfo,
          intermediateMaterial := Some(intermediateOutput.intermediateMaterial)
        )
      );
    } else {
      assert false;
    }
  }

  // Given decryption materials, unwrap and return the pdk and associated materials,
  // according to the Edk Wrapping Algorithm indicated in the algorithm suite.
  // The keyring can then use that information to populate the decryption
  // materials appropriately.
  // Generic type T can be utilized to pass information from the unwrapping procedure
  // back to the caller.
  method UnwrapEdkMaterial<T>(
    wrappedMaterial: seq<uint8>,
    decryptionMaterials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
    unwrap: UnwrapMaterial<T>
  ) returns (ret: Result<UnwrapEdkMaterialOutput<T>, Types.Error>)
    requires unwrap.Invariant()
    modifies unwrap.Modifies

    ensures ret.Failure? && decryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING? ==>
      unwrap.Ensures(
        UnwrapInput(
          wrappedMaterial := wrappedMaterial,
          algorithmSuite := decryptionMaterials.algorithmSuite,
          encryptionContext := decryptionMaterials.encryptionContext),
        Failure(ret.error),
        [])

    ensures ret.Success? ==>
      && var maybeProviderWrappedMaterial := GetProviderWrappedMaterial(wrappedMaterial, decryptionMaterials.algorithmSuite);
      && maybeProviderWrappedMaterial.Success?
      && (decryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping? ==>
          ret.value.intermediateMaterial.Some?)
      && var unwrapRes := UnwrapOutput(
        unwrappedMaterial :=
          if decryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING? then
            ret.value.plaintextDataKey
          else
            ret.value.intermediateMaterial.value,
        unwrapInfo := ret.value.unwrapInfo);
      && unwrap.Ensures(
        UnwrapInput(
          wrappedMaterial := maybeProviderWrappedMaterial.value,
          algorithmSuite := decryptionMaterials.algorithmSuite,
          encryptionContext := decryptionMaterials.encryptionContext),
        Success(unwrapRes),
        [])
  {
    :- Need(Materials.ValidDecryptionMaterials(decryptionMaterials),
      Types.AwsCryptographicMaterialProvidersException(
        message := "Invalid materials for decryption."));

    if (decryptionMaterials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?)  {
      var directOutput :- unwrap.Invoke(
        UnwrapInput(
          wrappedMaterial := wrappedMaterial,
          algorithmSuite := decryptionMaterials.algorithmSuite,
          encryptionContext := decryptionMaterials.encryptionContext
        ), []);

      return Success(
        UnwrapEdkMaterialOutput(
          plaintextDataKey := directOutput.unwrappedMaterial,
          symmetricSigningKey := None,
          unwrapInfo := directOutput.unwrapInfo,
          intermediateMaterial := None
        )
      );
    } else if (decryptionMaterials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?) {
      // Unwrap the EDK Ciphertext using the EdkWrapping method,
      // and obtain both the pdk and a symmetric signing key
      :- Need(|wrappedMaterial| >= (decryptionMaterials.algorithmSuite.encrypt.AES_GCM.keyLength +
          decryptionMaterials.algorithmSuite.encrypt.AES_GCM.tagLength) as int,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid material for Intermediate Unwrapping"));

      var intermediateOutput :- IntermediateUnwrap(
        unwrap := unwrap,
        wrappedMaterial := wrappedMaterial,
        algorithmSuite := decryptionMaterials.algorithmSuite,
        encryptionContext := decryptionMaterials.encryptionContext
      );

      return Success(
        UnwrapEdkMaterialOutput(
          plaintextDataKey := intermediateOutput.plaintextDataKey,
          symmetricSigningKey := Some(intermediateOutput.symmetricSigningKey),
          unwrapInfo := intermediateOutput.unwrapInfo,
          intermediateMaterial := Some(intermediateOutput.intermediateMaterial)
        )
      );
    } else {
      assert false;
    }
  }

  // Given material wrapped using Intermediate Key Wrapping,
  // get the provider wrapped portion
  function GetProviderWrappedMaterial(material: seq<uint8>, algSuite: Types.AlgorithmSuiteInfo)
  : (r: Result<seq<uint8>, Types.Error>)
    ensures r.Success? && algSuite.edkWrapping.DIRECT_KEY_WRAPPING? ==> r.value == material
    ensures r.Success? && algSuite.edkWrapping.IntermediateKeyWrapping? ==>
      var deserializedRes := DeserializeIntermediateWrappedMaterial(material, algSuite);
      && deserializedRes.Success?
      && r.value == deserializedRes.value.providerWrappedIkm
  {
    if algSuite.edkWrapping.DIRECT_KEY_WRAPPING? then
      Success(material)
    else
      assert algSuite.edkWrapping.IntermediateKeyWrapping?;
      var deserializedWrappedRes := DeserializeIntermediateWrappedMaterial(material, algSuite);
      if (deserializedWrappedRes.Failure?) then
        Failure(Types.AwsCryptographicMaterialProvidersException(
          message := "Unable to deserialize Intermediate Key Wrapped material."))
      else
        Success(deserializedWrappedRes.value.providerWrappedIkm)
  }
}
