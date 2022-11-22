// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

include "Keyrings/AwsKms/StrictMultiKeyring.dfy"
include "Keyrings/MultiKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsUtils.dfy"
include "Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/DiscoveryMultiKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsUtils.dfy"
include "Keyrings/AwsKms/MrkAwareStrictMultiKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/MrkAwareDiscoveryMultiKeyring.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "Keyrings/RawRSAKeyring.dfy"
include "CMMs/DefaultCMM.dfy"
include "DefaultClientSupplier.dfy"
include "Materials.dfy"
include "Commitment.dfy"
include "AlgorithmSuites.dfy"

module AwsCryptographyMaterialProvidersOperations refines AbstractAwsCryptographyMaterialProvidersOperations {

  import MultiKeyring
  import opened S = StrictMultiKeyring
  import opened D = DiscoveryMultiKeyring
  import opened MD = MrkAwareDiscoveryMultiKeyring
  import opened M = MrkAwareStrictMultiKeyring
  import AwsKmsKeyring
  import AwsKmsMrkKeyring
  import AwsKmsDiscoveryKeyring
  import AwsKmsMrkDiscoveryKeyring
  import RawAESKeyring
  import RawRSAKeyring
  import opened C = DefaultCMM
  import Crypto = AwsCryptographyPrimitivesTypes
  import Aws.Cryptography.Primitives
  import opened AwsKmsUtils
  import DefaultClientSupplier
  import Materials
  import Commitment
  import AlgorithmSuites

  datatype Config = Config(
    nameonly crypto: Primitives.AtomicPrimitivesClient
  )

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
  {
    && config.crypto.ValidState()
  }

  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {
    config.crypto.Modifies
  }

  predicate CreateAwsKmsKeyringEnsuresPublicly(input: CreateAwsKmsKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsKeyring(config: InternalConfig, input: CreateAwsKmsKeyringInput)
    returns (output: Result<IKeyring, Error>)
  {
    var _ :- ValidateKmsKeyId(input.kmsKeyId);
    var grantTokens :- GetValidGrantTokens(input.grantTokens);
    var keyring := new AwsKmsKeyring.AwsKmsKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
    return Success(keyring);
  }

  predicate CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsDiscoveryKeyring(config: InternalConfig, input: CreateAwsKmsDiscoveryKeyringInput)
    returns (output: Result<IKeyring, Error>)
  {
    if input.discoveryFilter.Some? {
      var _ :- ValidateDiscoveryFilter(input.discoveryFilter.value);
    }
    var grantTokens :- GetValidGrantTokens(input.grantTokens);
    var keyring := new AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring(input.kmsClient, input.discoveryFilter, grantTokens);
    return Success(keyring);
  }

  predicate CreateAwsKmsMultiKeyringEnsuresPublicly(input: CreateAwsKmsMultiKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsMultiKeyring(config: InternalConfig, input: CreateAwsKmsMultiKeyringInput)
    returns (output: Result<IKeyring, Error>)
  {
    var grantTokens :- GetValidGrantTokens(input.grantTokens);

    if input.clientSupplier.Some? {
      output := StrictMultiKeyring(
        input.generator,
        input.kmsKeyIds,
        input.clientSupplier.value,
        Option.Some(grantTokens)
      );
    } else {
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-multi-keyrings.md#aws-kms-multi-keyring
      //# If a regional client supplier is not passed, then a default MUST be
      //# created that takes a region string and generates a default AWS SDK
      //# client for the given region.
      var clientSupplier :- CreateDefaultClientSupplier(config, Types.CreateDefaultClientSupplierInput());
      output := StrictMultiKeyring(
        input.generator,
        input.kmsKeyIds,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }
  }

  predicate CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryMultiKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsDiscoveryMultiKeyring ( config: InternalConfig,  input: CreateAwsKmsDiscoveryMultiKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    var grantTokens :- GetValidGrantTokens(input.grantTokens);

    var clientSupplier: Types.IClientSupplier;

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-multi-keyrings.md#aws-kms-discovery-multi-keyring
    //# If a regional client supplier is not passed, then a default MUST be created that takes a region string and generates a default AWS SDK client for the given region.
    if input.clientSupplier.None? {
      clientSupplier :- CreateDefaultClientSupplier(config, Types.CreateDefaultClientSupplierInput());
    } else {
      clientSupplier := input.clientSupplier.value;
    }
    output := DiscoveryMultiKeyring(
      input.regions,
      input.discoveryFilter,
      clientSupplier,
      Option.Some(grantTokens)
    );
  }

  predicate CreateAwsKmsMrkKeyringEnsuresPublicly(input: CreateAwsKmsMrkKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsMrkKeyring ( config: InternalConfig,  input: CreateAwsKmsMrkKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    var _ :- ValidateKmsKeyId(input.kmsKeyId);
    var grantTokens :- GetValidGrantTokens(input.grantTokens);
    var keyring := new AwsKmsMrkKeyring.AwsKmsMrkKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
    return Success(keyring);
  }


  predicate CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkMultiKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsMrkMultiKeyring ( config: InternalConfig,  input: CreateAwsKmsMrkMultiKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    var grantTokens :- GetValidGrantTokens(input.grantTokens);

    var clientSupplier: Types.IClientSupplier;

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
    //# If a regional client supplier is not passed, then a default MUST be created that takes a region string and generates a default AWS SDK client for the given region.
    if input.clientSupplier.None? {
      clientSupplier :- CreateDefaultClientSupplier(config, Types.CreateDefaultClientSupplierInput());
    } else {
      clientSupplier := input.clientSupplier.value;
    }
    output := MrkAwareStrictMultiKeyring(
      input.generator,
      input.kmsKeyIds,
      clientSupplier,
      Option.Some(grantTokens)
    );
  }

  predicate CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsMrkDiscoveryKeyring ( config: InternalConfig,  input: CreateAwsKmsMrkDiscoveryKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    if input.discoveryFilter.Some? {
      var _ :- ValidateDiscoveryFilter(input.discoveryFilter.value);
    }

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#initialization
    //= type=implication
    //# The keyring SHOULD fail initialization if the provided region does not match the
    //# region of the KMS client.
    var regionMatch := AwsKmsUtils.RegionMatch(input.kmsClient, input.region);
    :- Need(regionMatch != Some(false),
      Types.AwsCryptographicMaterialProvidersException(
        message := "Provided client and region do not match"));

    var grantTokens :- GetValidGrantTokens(input.grantTokens);
    var keyring := new AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring(input.kmsClient, input.region, input.discoveryFilter, grantTokens);
    return Success(keyring);
  }


  predicate CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryMultiKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateAwsKmsMrkDiscoveryMultiKeyring ( config: InternalConfig,  input: CreateAwsKmsMrkDiscoveryMultiKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    var grantTokens :- GetValidGrantTokens(input.grantTokens);

    var clientSupplier: Types.IClientSupplier;

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
    //# If a regional client supplier is not passed,
    //# then a default MUST be created that takes a region string and
    //# generates a default AWS SDK client for the given region.
    if input.clientSupplier.None? {
      clientSupplier :- CreateDefaultClientSupplier(config, Types.CreateDefaultClientSupplierInput());
    } else {
      clientSupplier := input.clientSupplier.value;
    }
    output := MrkAwareDiscoveryMultiKeyring(
      input.regions,
      input.discoveryFilter,
      clientSupplier,
      Option.Some(grantTokens)
    );
  }

  predicate CreateMultiKeyringEnsuresPublicly(input: CreateMultiKeyringInput, output: Result<IKeyring, Error>)
  {true}

  method CreateMultiKeyring ( config: InternalConfig,  input: CreateMultiKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    :- Need(input.generator.Some? || |input.childKeyrings| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Must include a generator keyring and/or at least one child keyring"));

    var keyring := new MultiKeyring.MultiKeyring(input.generator, input.childKeyrings);
    return Success(keyring);
  }


  predicate CreateRawAesKeyringEnsuresPublicly(input: CreateRawAesKeyringInput, output: Result<IKeyring, Error>)
  {
    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#changelog
    //= type=implication
    //# Raw AES keyring MUST NOT accept a key namespace of "aws-kms".
      input.keyNamespace == "aws-kms"
    ==>
      output.Failure?
  }

  method CreateRawAesKeyring ( config: InternalConfig,  input: CreateRawAesKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    :- Need(input.keyNamespace != "aws-kms",
      Types.AwsCryptographicMaterialProvidersException(
        message := "keyNamespace must not be `aws-kms`"));

    var wrappingAlg:Crypto.AES_GCM := match input.wrappingAlg
      case ALG_AES128_GCM_IV12_TAG16 => Crypto.AES_GCM(
          keyLength := 16,
          tagLength := 16,
          ivLength := 12
        )
      case ALG_AES192_GCM_IV12_TAG16 => Crypto.AES_GCM(
          keyLength := 24,
          tagLength := 16,
          ivLength := 12
        )
      case ALG_AES256_GCM_IV12_TAG16 => Crypto.AES_GCM(
          keyLength := 32,
          tagLength := 16,
          ivLength := 12
        );

    var namespaceAndName :- ParseKeyNamespaceAndName(input.keyNamespace, input.keyName);
    var (namespace, name) := namespaceAndName;

    :- Need(|input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Invalid wrapping key length"));
    :- Need(|input.wrappingKey| == wrappingAlg.keyLength as int,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Wrapping key length does not match specified wrapping algorithm"));

    var keyring := new RawAESKeyring
      .RawAESKeyring(
        namespace := namespace,
        name := name,
        key := input.wrappingKey,
        wrappingAlgorithm := wrappingAlg,
        cryptoPrimitives := config.crypto
      );
    return Success(keyring);
  }


  predicate CreateRawRsaKeyringEnsuresPublicly(input: CreateRawRsaKeyringInput, output: Result<IKeyring, Error>)
  {
    //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#changelog
    //= type=implication
    //# Raw RSA keyring MUST NOT accept a key namespace of "aws-kms".
    && (input.keyNamespace == "aws-kms"
    ==>
      output.Failure?)
    && (input.publicKey.None? && input.privateKey.None?
      ==>
        output.Failure?)
  }

  method CreateRawRsaKeyring ( config: InternalConfig,  input: CreateRawRsaKeyringInput )
    returns (output: Result<IKeyring, Error>)
  {
    :- Need(input.keyNamespace != "aws-kms",
        Types.AwsCryptographicMaterialProvidersException(
      message := "keyNamespace must not be `aws-kms`"));
    :- Need(input.publicKey.Some? || input.privateKey.Some?,
        Types.AwsCryptographicMaterialProvidersException(
      message := "A publicKey or a privateKey is required"));

    var padding: Crypto.RSAPaddingMode := match input.paddingScheme
      case PKCS1 => Crypto.RSAPaddingMode.PKCS1
      case OAEP_SHA1_MGF1 => Crypto.RSAPaddingMode.OAEP_SHA1
      case OAEP_SHA256_MGF1 => Crypto.RSAPaddingMode.OAEP_SHA256
      case OAEP_SHA384_MGF1 => Crypto.RSAPaddingMode.OAEP_SHA384
      case OAEP_SHA512_MGF1 => Crypto.RSAPaddingMode.OAEP_SHA512
    ;

    var namespaceAndName :- ParseKeyNamespaceAndName(input.keyNamespace, input.keyName);
    var (namespace, name) := namespaceAndName;

    var keyring := new RawRSAKeyring.RawRSAKeyring(
      namespace := namespace,
      name := name,
      publicKey := input.publicKey,
      privateKey := input.privateKey,
      paddingScheme := padding,
      cryptoPrimitives := config.crypto
    );
    return Success(keyring);
  }
 

  predicate CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input: CreateDefaultCryptographicMaterialsManagerInput, output: Result<ICryptographicMaterialsManager, Error>)
  {true}

  method CreateDefaultCryptographicMaterialsManager(config: InternalConfig, input: CreateDefaultCryptographicMaterialsManagerInput)
    returns (output: Result<ICryptographicMaterialsManager, Error>)
  {
    var cmm := new DefaultCMM.OfKeyring(input.keyring, config.crypto);
    return Success(cmm);
  }

  predicate CreateDefaultClientSupplierEnsuresPublicly(input: CreateDefaultClientSupplierInput, output: Result<IClientSupplier, Error>)
  {true}

  method CreateDefaultClientSupplier ( config: InternalConfig,  input: CreateDefaultClientSupplierInput )
    returns (output: Result<IClientSupplier, Error>)
  {
    var clientSupplier := new DefaultClientSupplier.DefaultClientSupplier();
    return Success(clientSupplier);
  }

  function method InitializeEncryptionMaterials ( config: InternalConfig,  input: InitializeEncryptionMaterialsInput )
  : (output: Result<EncryptionMaterials, Error>)
  {
    Materials.InitializeEncryptionMaterials(input)
  }

  function method InitializeDecryptionMaterials ( config: InternalConfig,  input: InitializeDecryptionMaterialsInput )
  : (output: Result<DecryptionMaterials, Error>)
  {
    Materials.InitializeDecryptionMaterials(input)
  }

  function method ValidEncryptionMaterialsTransition ( config: InternalConfig,  input: ValidEncryptionMaterialsTransitionInput )
  : (output: Result<(), Error>)
  {
    :- Need(
      Materials.ValidEncryptionMaterialsTransition(input.start, input.stop),
      InvalidEncryptionMaterialsTransition( message := "Invalid Encryption Materials Transition" )
    );
    
    Success(())
  }

  function method ValidDecryptionMaterialsTransition ( config: InternalConfig,  input: ValidDecryptionMaterialsTransitionInput )
  : (output: Result<(), Error>)
  {
    :- Need(
      Materials.DecryptionMaterialsTransitionIsValid(input.start, input.stop),
      InvalidDecryptionMaterialsTransition( message := "Invalid Decryption Materials Transition")
    );

    Success(())
  }

  function method EncryptionMaterialsHasPlaintextDataKey ( config: InternalConfig,  input: EncryptionMaterials )
    : (output: Result<(), Error>)
  {
    :- Need(
      Materials.EncryptionMaterialsHasPlaintextDataKey(input),
      InvalidDecryptionMaterials( message := "Invalid Encryption Materials")
    );

    Success(())
  }
  function method DecryptionMaterialsWithPlaintextDataKey ( config: InternalConfig,  input: DecryptionMaterials )
    : (output: Result<(), Error>)
  {
    :- Need(
      Materials.DecryptionMaterialsWithPlaintextDataKey(input),
      InvalidDecryptionMaterials( message := "Invalid Decryption Materials")
    );

    Success(())
  }

  function method GetAlgorithmSuiteInfo ( config: InternalConfig,  input: seq<uint8> )
  : (output: Result<AlgorithmSuiteInfo, Error>)
  {
    AlgorithmSuites.GetAlgorithmSuiteInfo(input)
  }

  function method ValidAlgorithmSuiteInfo ( config: InternalConfig,  input: AlgorithmSuiteInfo )
  : (output: Result<(), Error>)
  {
    :- Need(AlgorithmSuites.AlgorithmSuite?(input),
      InvalidAlgorithmSuiteInfo( message := "Invalid AlgorithmSuiteInfo" )
    );

    Success(())
  }

  function method ValidateCommitmentPolicyOnEncrypt ( config: InternalConfig,  input: ValidateCommitmentPolicyOnEncryptInput )
  : (output: Result<(), Error>)
  {
    :- Commitment.ValidateCommitmentPolicyOnEncrypt(input.algorithm, input.commitmentPolicy);

    Success(())
  }

  function method ValidateCommitmentPolicyOnDecrypt ( config: InternalConfig,  input: ValidateCommitmentPolicyOnDecryptInput )
  : (output: Result<(), Error>)
  {
    :- Commitment.ValidateCommitmentPolicyOnDecrypt(input.algorithm, input.commitmentPolicy);

    Success(())
  }

}
