// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../Materials.dfy"
include "MaterialWrapping.dfy"
include "../Keyrings/RawAESKeyring.dfy"

module IntermediateKeyWrapping {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Actions
  import opened Wrappers
  import opened MaterialWrapping
  import opened AlgorithmSuites
  import Crypto = AwsCryptographyPrimitivesTypes
  import Types = AwsCryptographyMaterialProvidersTypes
  import Aws.Cryptography.Primitives
  import Materials
  import UTF8
  import HKDF
  import RawAESKeyring // TODO centralize EC serialization

  const KEYWRAP_MAC_INFO := UTF8.EncodeAscii("AWS_MPL_INTERMEDIATE_KEYWRAP_MAC");
  const KEYWRAP_ENC_INFO := UTF8.EncodeAscii("AWS_MPL_INTERMEDIATE_KEYWRAP_ENC");

  datatype IntermediateUnwrapOutput<T> = IntermediateUnwrapOutput(
    nameonly plaintextDataKey: seq<uint8>,
    nameonly symmetricSigningKey: seq<uint8>,
    nameonly unwrapInfo: T,
    nameonly ghost intermediateMaterial: seq<uint8>
  )

  datatype IntermediateGenerateAndWrapOutput<T> = IntermediateGenerateAndWrapOutput(
    nameonly plaintextDataKey: seq<uint8>,
    nameonly wrappedMaterial: seq<uint8>,
    nameonly symmetricSigningKey: seq<uint8>,
    nameonly wrapInfo: T,
    nameonly ghost intermediateMaterial: seq<uint8>
  )

  datatype IntermediateWrapOutput<T> = IntermediateWrapOutput(
    nameonly wrappedMaterial: seq<uint8>,
    nameonly symmetricSigningKey: seq<uint8>,
    nameonly wrapInfo: T,
    nameonly ghost intermediateMaterial: seq<uint8>
  )

  method IntermediateUnwrap<T>(
    unwrap: UnwrapMaterial<T>,
    wrappedMaterial: seq<uint8>,
    algorithmSuite: Types.AlgorithmSuiteInfo,
    encryptionContext: Types.EncryptionContext
  ) returns (res: Result<IntermediateUnwrapOutput<T>, Types.Error>)
    requires unwrap.Invariant()
    requires |wrappedMaterial| >=
      (AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) + AlgorithmSuites.GetEncryptTagLength(algorithmSuite)) as nat
    requires algorithmSuite.commitment.HKDF?
    modifies unwrap.Modifies
    ensures res.Success? ==> |res.value.plaintextDataKey| == AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) as nat
    ensures
      res.Success? ==>
        && var maybeIntermediateWrappedMat := DeserializeIntermediateWrappedMaterial(wrappedMaterial, algorithmSuite);
        && maybeIntermediateWrappedMat.Success?
        && var unwrapRes := UnwrapOutput(
          unwrappedMaterial := res.value.intermediateMaterial,
          unwrapInfo := res.value.unwrapInfo);
        && unwrap.Ensures(
          UnwrapInput(
            wrappedMaterial := maybeIntermediateWrappedMat.value.providerWrappedIkm,
            encryptionContext := encryptionContext,
            algorithmSuite := algorithmSuite),
          Success(unwrapRes),
          [])

  {
    // TODO pass in the crypto client instead so that we can prove things about it's usage
    var maybeCrypto := Primitives.AtomicPrimitives();
    var cryptoPrimitives :- maybeCrypto
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));

    // Deserialize the Intermediate-Wrapped material
    var deserializedWrapped :- DeserializeIntermediateWrappedMaterial(wrappedMaterial, algorithmSuite);
    var DeserializedIntermediateWrappedMaterial(encryptedPdk, providerWrappedIkm) := deserializedWrapped;
 
    var unwrapOutput :- unwrap.Invoke(
      UnwrapInput(
        wrappedMaterial := providerWrappedIkm,
        encryptionContext := encryptionContext,
        algorithmSuite := algorithmSuite
      ), []); 
    var UnwrapOutput(intermediateMaterial, unwrapInfo) := unwrapOutput;
 
    var derivedKeys :- DeriveKeysFromIntermediateMaterial(
      intermediateMaterial,
      algorithmSuite,
      encryptionContext,
      cryptoPrimitives
    );
    var PdkEncryptionAndSymmetricSigningKeys(pdkEncryptionKey, symmetricSigningKey) := derivedKeys;
 
    // Decrypt the plaintext data key with the pdkEncryptionKey
    var iv: seq<uint8> := seq(AlgorithmSuites.GetEncryptIvLength(algorithmSuite) as nat, _ => 0); // IV is zero
    var tagIndex := |encryptedPdk| - AlgorithmSuites.GetEncryptTagLength(algorithmSuite) as nat;
    var aad :- RawAESKeyring.EncryptionContextToAAD(encryptionContext); // TODO centralize EC serialization

    var decInput := Crypto.AESDecryptInput(
      encAlg := algorithmSuite.encrypt.AES_GCM,
      iv := iv,
      key := pdkEncryptionKey,
      cipherTxt := encryptedPdk[..tagIndex],
      authTag := encryptedPdk[tagIndex..],
      aad := aad
    );
    var decOutR := cryptoPrimitives.AESDecrypt(decInput);
    var plaintextDataKey :- decOutR.MapFailure(e => Types.AwsCryptographyPrimitives(e));

    :- Need(|plaintextDataKey| == AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) as nat,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Unexpected AES_GCM Decrypt length"));
 
    return Success(IntermediateUnwrapOutput(
      plaintextDataKey := plaintextDataKey,
      symmetricSigningKey := symmetricSigningKey,
      unwrapInfo := unwrapInfo,
      intermediateMaterial := intermediateMaterial
    ));
  }

  method IntermediateWrap<T>(
    generateAndWrap: GenerateAndWrapMaterial<T>,
    plaintextDataKey: seq<uint8>,
    algorithmSuite: Types.AlgorithmSuiteInfo,
    encryptionContext: Types.EncryptionContext
  ) returns (res: Result<IntermediateWrapOutput<T>, Types.Error>)
    requires generateAndWrap.Invariant()
    requires algorithmSuite.commitment.HKDF?
    requires |plaintextDataKey| == AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) as nat
    modifies generateAndWrap.Modifies
    ensures
      res.Success? ==>
        && var maybeIntermediateWrappedMat :=
            DeserializeIntermediateWrappedMaterial(res.value.wrappedMaterial, algorithmSuite);
        && maybeIntermediateWrappedMat.Success?
        && generateAndWrap.Ensures(
          GenerateAndWrapInput(
            algorithmSuite := algorithmSuite,
            encryptionContext := encryptionContext),
          Success(
            GenerateAndWrapOutput(
              plaintextMaterial := res.value.intermediateMaterial,
              wrappedMaterial := maybeIntermediateWrappedMat.value.providerWrappedIkm,
              wrapInfo := res.value.wrapInfo)),
          [])

        //= aws-encryption-sdk-specification/framework/algorithm-suites.md#intermediate-key-wrapping
        //# - The [EDK ciphertext](./structures.md#ciphertext) MUST be the following serialization:
        //  | Field                      | Length (bytes)                                     | Interpreted as |
        //  | -------------------------- | -------------------------------------------------- | -------------- |
        //  | Wrapped Plaintext Data Key | The algorithm suite's encryption key length + 12   | Bytes          |
        //  | Wrapped Intermediate Key   | Determined by the keyring responsible for wrapping | Bytes          |
        && res.value.wrappedMaterial ==
            maybeIntermediateWrappedMat.value.encryptedPdk + maybeIntermediateWrappedMat.value.providerWrappedIkm

        //= aws-encryption-sdk-specification/framework/algorithm-suites.md#wrapped-plaintext-data-key
        //= type=implication
        //# This value MUST be equal to the algorithm suite's encryption key length + 12.
        && |maybeIntermediateWrappedMat.value.encryptedPdk| ==
            (AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) + AlgorithmSuites.GetEncryptTagLength(algorithmSuite)) as nat
  {
    // TODO pass in the crypto client instead so that we can prove things about it's usage
    var maybeCrypto := Primitives.AtomicPrimitives();
    var cryptoPrimitives :- maybeCrypto
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));

    // Use the provider to get the intermediate key material, and wrapped intermediate key material
    var generateAndWrapOutput :- generateAndWrap.Invoke(
      GenerateAndWrapInput(
        algorithmSuite := algorithmSuite,
        encryptionContext := encryptionContext
      ), []);

    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#intermediate-key-wrapping
    //# - For each encrypted data key, a distinct `intermediate key` MUST be generated using cryptographically secure random bytes.
    var GenerateAndWrapOutput(intermediateMaterial, providerWrappedIkm, wrapInfo) := generateAndWrapOutput;

    var derivedKeys :- DeriveKeysFromIntermediateMaterial(
      intermediateMaterial,
      algorithmSuite,
      encryptionContext,
      cryptoPrimitives
    );
    var PdkEncryptionAndSymmetricSigningKeys(pdkEncryptionKey, symmetricSigningKey) := derivedKeys;

    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#wrapped-plaintext-data-key
    //# The wrapped plaintext data key MUST be the result of the following AES GCM 256 Encrypt operation:
    //  - Plaintext: the [plaintext data key](./structures.md#plaintext-data-key) in the related encryption or decryption materials.
    //  - Encryption key: The `key encryption key` derived above.
    //  - AAD: The [enccryption context](./structures.md#encryption-context) in the related encryption or decryption materials,
    //    serialized according to the the [ESDK message header](../data-format/message-header.md#aad).
    var iv: seq<uint8> := seq(AlgorithmSuites.GetEncryptIvLength(algorithmSuite) as nat, _ => 0); // IV is zero
    var aad :- RawAESKeyring.EncryptionContextToAAD(encryptionContext); // TODO centralize EC serialization
    var encInput := Crypto.AESEncryptInput(
      encAlg := algorithmSuite.encrypt.AES_GCM,
      iv := iv,
      key := pdkEncryptionKey,
      msg := plaintextDataKey,
      aad := aad
    );
    var encOutR := cryptoPrimitives.AESEncrypt(encInput);
    var encryptedPdk :- encOutR.MapFailure(e => Types.AwsCryptographyPrimitives(e));

    :- Need(|encryptedPdk.cipherText + encryptedPdk.authTag| ==
        (AlgorithmSuites.GetEncryptKeyLength(algorithmSuite) + AlgorithmSuites.GetEncryptTagLength(algorithmSuite)) as nat,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Unexpected AES_GCM Encrypt length"));

    var serializedMaterial := encryptedPdk.cipherText + encryptedPdk.authTag + providerWrappedIkm;

    return Success(IntermediateWrapOutput(
      wrappedMaterial := serializedMaterial,
      symmetricSigningKey := symmetricSigningKey,
      wrapInfo := wrapInfo,
      intermediateMaterial := intermediateMaterial
    ));
  }

  method IntermediateGenerateAndWrap<T>(
    generateAndWrap: GenerateAndWrapMaterial<T>,
    algorithmSuite: Types.AlgorithmSuiteInfo,
    encryptionContext: Types.EncryptionContext
  ) returns (res: Result<IntermediateGenerateAndWrapOutput<T>, Types.Error>)
    requires generateAndWrap.Invariant()
    requires algorithmSuite.commitment.HKDF?
    modifies generateAndWrap.Modifies
    ensures
      res.Success? ==>
        && var maybeIntermediateWrappedMat :=
            DeserializeIntermediateWrappedMaterial(res.value.wrappedMaterial, algorithmSuite);
        && maybeIntermediateWrappedMat.Success?
        && generateAndWrap.Ensures(GenerateAndWrapInput(
          algorithmSuite := algorithmSuite,
          encryptionContext := encryptionContext
        ), Success(
          GenerateAndWrapOutput(
            plaintextMaterial := res.value.intermediateMaterial,
            wrappedMaterial := maybeIntermediateWrappedMat.value.providerWrappedIkm,
            wrapInfo := res.value.wrapInfo)),
        [])
  {
    // TODO pass in the crypto client instead so that we can prove things about it's usage
    var maybeCrypto := Primitives.AtomicPrimitives();
    var cryptoPrimitives :- maybeCrypto
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));

    var generateBytesResult := cryptoPrimitives
      .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(algorithmSuite)));
    var plaintextDataKey :- generateBytesResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

    var wrapOutput :- IntermediateWrap(
      generateAndWrap,
      plaintextDataKey,
      algorithmSuite,
      encryptionContext
    );

    return Success(IntermediateGenerateAndWrapOutput(
      plaintextDataKey := plaintextDataKey,
      wrappedMaterial := wrapOutput.wrappedMaterial,
      symmetricSigningKey := wrapOutput.symmetricSigningKey,
      wrapInfo := wrapOutput.wrapInfo,
      intermediateMaterial := wrapOutput.intermediateMaterial
    ));
  }

  datatype DeserializedIntermediateWrappedMaterial = DeserializedIntermediateWrappedMaterial(
    nameonly encryptedPdk: seq<uint8>,
    nameonly providerWrappedIkm: seq<uint8>
  )

  // Given material wrapped using Intermediate Key Wrapping,
  // get the provider wrapped portion
  function method DeserializeIntermediateWrappedMaterial(material: seq<uint8>, algSuite: Types.AlgorithmSuiteInfo)
  : (ret: Result<DeserializedIntermediateWrappedMaterial, Types.Error>)
  {
    :- Need(|material| >= (AlgorithmSuites.GetEncryptKeyLength(algSuite) + AlgorithmSuites.GetEncryptTagLength(algSuite)) as nat,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Unable to deserialize Intermediate Key Wrapped material: too short."));
    var encryptedPdkLen := AlgorithmSuites.GetEncryptKeyLength(algSuite) + AlgorithmSuites.GetEncryptTagLength(algSuite);
    Success(DeserializedIntermediateWrappedMaterial(
      encryptedPdk := material[..encryptedPdkLen],
      providerWrappedIkm := material[encryptedPdkLen..]
    ))
  }

  datatype PdkEncryptionAndSymmetricSigningKeys = PdkEncryptionAndSymmetricSigningKeys(
    nameonly pdkEncryptionKey: seq<uint8>,
    nameonly symmetricSigningKey: seq<uint8>
  )

  method DeriveKeysFromIntermediateMaterial(
      intermediateMaterial: seq<uint8>,
      algorithmSuite: Types.AlgorithmSuiteInfo,
      encryptionContext: Types.EncryptionContext,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      returns (res: Result<PdkEncryptionAndSymmetricSigningKeys, Types.Error>)
    requires cryptoPrimitives.ValidState()
    requires algorithmSuite.commitment.HKDF?
    modifies cryptoPrimitives.Modifies
    ensures cryptoPrimitives.ValidState()
  {
    var hkdfExtractInput := Crypto.HkdfExtractInput(
      digestAlgorithm := algorithmSuite.commitment.HKDF.hmac,
      salt := None,
      ikm := intermediateMaterial
    );

    var maybePseudoRandomKey := cryptoPrimitives.HkdfExtract(hkdfExtractInput);
    var pseudoRandomKey :- maybePseudoRandomKey
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));

    var symmetricSigningKeyInput := Crypto.HkdfExpandInput(
      digestAlgorithm := algorithmSuite.commitment.HKDF.hmac,
      prk := pseudoRandomKey,
      info := KEYWRAP_MAC_INFO,
      expectedLength := algorithmSuite.commitment.HKDF.outputKeyLength
    );
    var pdkEncryptionKeyInput := symmetricSigningKeyInput.(
      info := KEYWRAP_ENC_INFO
    );

    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#intermediate-key-wrapping
    //# - For each encrypted data key, a [symmetric signing key](./structures.md#symmetric-signing-key) MUST be derived from the `intermediate key`
    //# using the key derivation algorithm in the algorithm suite, with the following specifics:
    //  - The input key material is the `intermediate key`
    //  - The salt is empty
    //  - The info is "AWS_MPL_INTERMEDIATE_KEYWRAP_MAC" as UTF8 bytes.
    var maybeSymmetricSigningKey := cryptoPrimitives.HkdfExpand(symmetricSigningKeyInput);
    var symmetricSigningKey :- maybeSymmetricSigningKey
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));
    
    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#intermediate-key-wrapping
    //# - For each encrypted data key, a `key encryption key` MUST be derived from the `intermediate key`
    //# using the key derivation algorithm in the algorithm suite, with the following specifics:
    //  - The input key material is the `intermediate key`
    //  - The salt is empty
    //  - The info is "AWS_MPL_INTERMEDIATE_KEYWRAP_ENC" as UTF8 bytes.
    var maybePdkEncryptionKey := cryptoPrimitives.HkdfExpand(pdkEncryptionKeyInput);
    var pdkEncryptionKey :- maybePdkEncryptionKey
      .MapFailure(e => Types.AwsCryptographyPrimitives(e));

    return Success(
      PdkEncryptionAndSymmetricSigningKeys(
        pdkEncryptionKey := pdkEncryptionKey,
        symmetricSigningKey := symmetricSigningKey
      )
    );
  }
}
