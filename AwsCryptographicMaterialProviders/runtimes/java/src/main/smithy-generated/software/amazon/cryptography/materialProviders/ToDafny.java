// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.*;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring;
import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.ECDSASignatureAlgorithm;
import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDB__20120810Client;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec;
import Wrappers_Compile.Option;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Byte;
import java.lang.Character;
import java.lang.IllegalArgumentException;
import java.lang.Integer;
import java.lang.Long;
import java.lang.RuntimeException;
import java.lang.String;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialProviders.model.CollectionOfErrors;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.NativeError;
import software.amazon.cryptography.materialProviders.model.OpaqueError;
import software.amazon.cryptography.materialProviders.model.DIRECT_KEY_WRAPPING;

public class ToDafny {
  public static Error Error(NativeError nativeValue) {
    if (nativeValue instanceof InvalidDecryptionMaterials) {
      return ToDafny.Error((InvalidDecryptionMaterials) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfo) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfo) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnEncrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnEncrypt) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterials) {
      return ToDafny.Error((InvalidEncryptionMaterials) nativeValue);
    }
    if (nativeValue instanceof InvalidDecryptionMaterialsTransition) {
      return ToDafny.Error((InvalidDecryptionMaterialsTransition) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterialsTransition) {
      return ToDafny.Error((InvalidEncryptionMaterialsTransition) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnDecrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnDecrypt) nativeValue);
    }
    if (nativeValue instanceof AwsCryptographicMaterialProvidersException) {
      return ToDafny.Error((AwsCryptographicMaterialProvidersException) nativeValue);
    }
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list = software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(), 
        ToDafny::Error, 
        Error._typeDescriptor());
    return Error.create_Collection(list);
  }

  public static OnEncryptInput OnEncryptInput(
      software.amazon.cryptography.materialProviders.model.OnEncryptInput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptInput(materials);
  }

  public static CreateAwsKmsKeyringInput CreateAwsKmsKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null);
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsKeyringInput(kmsKeyId, kmsClient, grantTokens);
  }

  public static GetEncryptionMaterialsOutput GetEncryptionMaterialsOutput(
      software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput nativeValue) {
    EncryptionMaterials encryptionMaterials;
    encryptionMaterials = ToDafny.EncryptionMaterials(nativeValue.encryptionMaterials());
    return new GetEncryptionMaterialsOutput(encryptionMaterials);
  }

  public static CreateAwsKmsMrkDiscoveryKeyringInput CreateAwsKmsMrkDiscoveryKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryKeyringInput nativeValue) {
    IKeyManagementServiceClient kmsClient;
    kmsClient = new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null);
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    DafnySequence<? extends Character> region;
    region = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.region());
    return new CreateAwsKmsMrkDiscoveryKeyringInput(kmsClient, discoveryFilter, grantTokens, region);
  }


  public static CreateAwsKmsHierarchicalKeyringInput CreateAwsKmsHierarchyKeyringInput(
          software.amazon.cryptography.materialProviders.model.CreateAwsKmsHierarchicalKeyringInput nativeValue) {
    DafnySequence<? extends Character> branchKeyId;
    branchKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyId());
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null);
    IDynamoDB__20120810Client ddbClient;
    ddbClient = new Dafny.Com.Amazonaws.Dynamodb.Shim(nativeValue.ddbClient(), null);
    DafnySequence<? extends Character> branchKeysTableName;
    branchKeysTableName = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeysTableName());
    Long ttlMilliseconds;
    ttlMilliseconds = (nativeValue.ttlMilliseconds());
    Option<Integer> maxCacheSize;
    maxCacheSize = Objects.nonNull(nativeValue.maxCacheSize()) ?
            Option.create_Some((nativeValue.maxCacheSize()))
            : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
            Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
            : Option.create_None();
    return new CreateAwsKmsHierarchicalKeyringInput(branchKeyId, kmsKeyId, kmsClient, ddbClient, branchKeysTableName, ttlMilliseconds, maxCacheSize, grantTokens);
  }

  public static IDENTITY IDENTITY(
      software.amazon.cryptography.materialProviders.model.IDENTITY nativeValue) {
    return new IDENTITY();
  }

  public static CreateAwsKmsMrkKeyringInput CreateAwsKmsMrkKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null);
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkKeyringInput(kmsKeyId, kmsClient, grantTokens);
  }

  public static CreateAwsKmsDiscoveryKeyringInput CreateAwsKmsDiscoveryKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryKeyringInput nativeValue) {
    IKeyManagementServiceClient kmsClient;
    kmsClient = new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null);
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsDiscoveryKeyringInput(kmsClient, discoveryFilter, grantTokens);
  }

  public static CreateAwsKmsRsaKeyringInput CreateAwsKmsRsaKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsRsaKeyringInput nativeValue) {
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.publicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.publicKey()))
        : Option.create_None();
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    EncryptionAlgorithmSpec encryptionAlgorithm;
    encryptionAlgorithm = Dafny.Com.Amazonaws.Kms.ToDafny.EncryptionAlgorithmSpec(nativeValue.encryptionAlgorithm());
    Option<IKeyManagementServiceClient> kmsClient;
    kmsClient = Objects.nonNull(nativeValue.kmsClient()) ?
        Option.create_Some((new Dafny.Com.Amazonaws.Kms.Shim(nativeValue.kmsClient(), null)))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsRsaKeyringInput(publicKey, kmsKeyId, encryptionAlgorithm, kmsClient, grantTokens);
  }

  public static ValidateCommitmentPolicyOnDecryptInput ValidateCommitmentPolicyOnDecryptInput(
      software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnDecryptInput nativeValue) {
    AlgorithmSuiteId algorithm;
    algorithm = ToDafny.AlgorithmSuiteId(nativeValue.algorithm());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    return new ValidateCommitmentPolicyOnDecryptInput(algorithm, commitmentPolicy);
  }

  public static DecryptionMaterials DecryptionMaterials(
      software.amazon.cryptography.materialProviders.model.DecryptionMaterials nativeValue) {
    AlgorithmSuiteInfo algorithmSuite;
    algorithmSuite = ToDafny.AlgorithmSuiteInfo(nativeValue.algorithmSuite());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    Option<DafnySequence<? extends Byte>> plaintextDataKey;
    plaintextDataKey = Objects.nonNull(nativeValue.plaintextDataKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.plaintextDataKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> verificationKey;
    verificationKey = Objects.nonNull(nativeValue.verificationKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey()))
        : Option.create_None();
    return new DecryptionMaterials(algorithmSuite, encryptionContext, plaintextDataKey, verificationKey);
  }

  public static InitializeDecryptionMaterialsInput InitializeDecryptionMaterialsInput(
      software.amazon.cryptography.materialProviders.model.InitializeDecryptionMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    return new InitializeDecryptionMaterialsInput(algorithmSuiteId, encryptionContext);
  }

  public static AlgorithmSuiteInfo AlgorithmSuiteInfo(
      software.amazon.cryptography.materialProviders.model.AlgorithmSuiteInfo nativeValue) {
    AlgorithmSuiteId id;
    id = ToDafny.AlgorithmSuiteId(nativeValue.id());
    DafnySequence<? extends Byte> binaryId;
    binaryId = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.binaryId());
    Integer messageVersion;
    messageVersion = (nativeValue.messageVersion());
    Encrypt encrypt;
    encrypt = ToDafny.Encrypt(nativeValue.encrypt());
    DerivationAlgorithm kdf;
    kdf = ToDafny.DerivationAlgorithm(nativeValue.kdf());
    DerivationAlgorithm commitment;
    commitment = ToDafny.DerivationAlgorithm(nativeValue.commitment());
    SignatureAlgorithm signature;
    signature = ToDafny.SignatureAlgorithm(nativeValue.signature());
    SymmetricSignatureAlgorithm symmetricSignature;
    symmetricSignature = ToDafny.SymmetricSignatureAlgorithm(nativeValue.symmetricSignature());
    EdkWrappingAlgorithm edkWrapping;
    edkWrapping = ToDafny.EdkWrappingAlgorithm(nativeValue.edkWrapping());
    return new AlgorithmSuiteInfo(id, binaryId, messageVersion, encrypt, kdf, commitment, signature, symmetricSignature, edkWrapping);
  }

  public static OnDecryptInput OnDecryptInput(
      software.amazon.cryptography.materialProviders.model.OnDecryptInput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    return new OnDecryptInput(materials, encryptedDataKeys);
  }

  public static EncryptedDataKey EncryptedDataKey(
      software.amazon.cryptography.materialProviders.model.EncryptedDataKey nativeValue) {
    DafnySequence<? extends Byte> keyProviderId;
    keyProviderId = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.keyProviderId());
    DafnySequence<? extends Byte> keyProviderInfo;
    keyProviderInfo = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.keyProviderInfo());
    DafnySequence<? extends Byte> ciphertext;
    ciphertext = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ciphertext());
    return new EncryptedDataKey(keyProviderId, keyProviderInfo, ciphertext);
  }

  public static MaterialProvidersConfig MaterialProvidersConfig(
      software.amazon.cryptography.materialProviders.model.MaterialProvidersConfig nativeValue) {
    return new MaterialProvidersConfig();
  }

  public static ValidEncryptionMaterialsTransitionInput ValidEncryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialProviders.model.ValidEncryptionMaterialsTransitionInput nativeValue) {
    EncryptionMaterials start;
    start = ToDafny.EncryptionMaterials(nativeValue.start());
    EncryptionMaterials stop;
    stop = ToDafny.EncryptionMaterials(nativeValue.stop());
    return new ValidEncryptionMaterialsTransitionInput(start, stop);
  }

  public static GetClientInput GetClientInput(
      software.amazon.cryptography.materialProviders.model.GetClientInput nativeValue) {
    DafnySequence<? extends Character> region;
    region = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.region());
    return new GetClientInput(region);
  }

  public static CreateRawRsaKeyringInput CreateRawRsaKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateRawRsaKeyringInput nativeValue) {
    DafnySequence<? extends Character> keyNamespace;
    keyNamespace = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.keyNamespace());
    DafnySequence<? extends Character> keyName;
    keyName = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.keyName());
    PaddingScheme paddingScheme;
    paddingScheme = ToDafny.PaddingScheme(nativeValue.paddingScheme());
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.publicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.publicKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> privateKey;
    privateKey = Objects.nonNull(nativeValue.privateKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.privateKey()))
        : Option.create_None();
    return new CreateRawRsaKeyringInput(keyNamespace, keyName, paddingScheme, publicKey, privateKey);
  }

  public static CreateDefaultCryptographicMaterialsManagerInput CreateDefaultCryptographicMaterialsManagerInput(
      software.amazon.cryptography.materialProviders.model.CreateDefaultCryptographicMaterialsManagerInput nativeValue) {
    IKeyring keyring;
    keyring = ToDafny.Keyring(nativeValue.keyring());
    return new CreateDefaultCryptographicMaterialsManagerInput(keyring);
  }

  public static GetEncryptionMaterialsInput GetEncryptionMaterialsInput(
      software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsInput nativeValue) {
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    Option<AlgorithmSuiteId> algorithmSuiteId;
    algorithmSuiteId = Objects.nonNull(nativeValue.algorithmSuiteId()) ?
        Option.create_Some(ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId()))
        : Option.create_None();
    Option<Long> maxPlaintextLength;
    maxPlaintextLength = Objects.nonNull(nativeValue.maxPlaintextLength()) ?
        Option.create_Some((nativeValue.maxPlaintextLength()))
        : Option.create_None();
    return new GetEncryptionMaterialsInput(encryptionContext, commitmentPolicy, algorithmSuiteId, maxPlaintextLength);
  }

  public static OnDecryptOutput OnDecryptOutput(
      software.amazon.cryptography.materialProviders.model.OnDecryptOutput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    return new OnDecryptOutput(materials);
  }

  public static OnEncryptOutput OnEncryptOutput(
      software.amazon.cryptography.materialProviders.model.OnEncryptOutput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptOutput(materials);
  }

  public static CreateAwsKmsMultiKeyringInput CreateAwsKmsMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMultiKeyringInput nativeValue) {
    Option<DafnySequence<? extends Character>> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.generator()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> kmsKeyIds;
    kmsKeyIds = Objects.nonNull(nativeValue.kmsKeyIds()) ?
        Option.create_Some(ToDafny.KmsKeyIdList(nativeValue.kmsKeyIds()))
        : Option.create_None();
    Option<IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsDiscoveryMultiKeyringInput CreateAwsKmsDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsMrkDiscoveryMultiKeyringInput CreateAwsKmsMrkDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static EncryptionMaterials EncryptionMaterials(
      software.amazon.cryptography.materialProviders.model.EncryptionMaterials nativeValue) {
    AlgorithmSuiteInfo algorithmSuite;
    algorithmSuite = ToDafny.AlgorithmSuiteInfo(nativeValue.algorithmSuite());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    Option<DafnySequence<? extends Byte>> plaintextDataKey;
    plaintextDataKey = Objects.nonNull(nativeValue.plaintextDataKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.plaintextDataKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> signingKey;
    signingKey = Objects.nonNull(nativeValue.signingKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey()))
        : Option.create_None();
    return new EncryptionMaterials(algorithmSuite, encryptionContext, encryptedDataKeys, plaintextDataKey, signingKey);
  }

  public static None None(software.amazon.cryptography.materialProviders.model.None nativeValue) {
    return new None();
  }

  public static HKDF HKDF(software.amazon.cryptography.materialProviders.model.HKDF nativeValue) {
    DigestAlgorithm hmac;
    hmac = software.amazon.cryptography.primitives.ToDafny.DigestAlgorithm(nativeValue.hmac());
    Integer saltLength;
    saltLength = (nativeValue.saltLength());
    Integer inputKeyLength;
    inputKeyLength = (nativeValue.inputKeyLength());
    Integer outputKeyLength;
    outputKeyLength = (nativeValue.outputKeyLength());
    return new HKDF(hmac, saltLength, inputKeyLength, outputKeyLength);
  }

  public static DecryptMaterialsOutput DecryptMaterialsOutput(
      software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput nativeValue) {
    DecryptionMaterials decryptionMaterials;
    decryptionMaterials = ToDafny.DecryptionMaterials(nativeValue.decryptionMaterials());
    return new DecryptMaterialsOutput(decryptionMaterials);
  }

  public static ValidateCommitmentPolicyOnEncryptInput ValidateCommitmentPolicyOnEncryptInput(
      software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnEncryptInput nativeValue) {
    AlgorithmSuiteId algorithm;
    algorithm = ToDafny.AlgorithmSuiteId(nativeValue.algorithm());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    return new ValidateCommitmentPolicyOnEncryptInput(algorithm, commitmentPolicy);
  }

  public static DiscoveryFilter DiscoveryFilter(
      software.amazon.cryptography.materialProviders.model.DiscoveryFilter nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> accountIds;
    accountIds = ToDafny.AccountIdList(nativeValue.accountIds());
    DafnySequence<? extends Character> partition;
    partition = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.partition());
    return new DiscoveryFilter(accountIds, partition);
  }

  public static InitializeEncryptionMaterialsInput InitializeEncryptionMaterialsInput(
      software.amazon.cryptography.materialProviders.model.InitializeEncryptionMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    Option<DafnySequence<? extends Byte>> signingKey;
    signingKey = Objects.nonNull(nativeValue.signingKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> verificationKey;
    verificationKey = Objects.nonNull(nativeValue.verificationKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey()))
        : Option.create_None();
    return new InitializeEncryptionMaterialsInput(algorithmSuiteId, encryptionContext, signingKey, verificationKey);
  }

  public static CreateAwsKmsMrkMultiKeyringInput CreateAwsKmsMrkMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkMultiKeyringInput nativeValue) {
    Option<DafnySequence<? extends Character>> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.generator()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> kmsKeyIds;
    kmsKeyIds = Objects.nonNull(nativeValue.kmsKeyIds()) ?
        Option.create_Some(ToDafny.KmsKeyIdList(nativeValue.kmsKeyIds()))
        : Option.create_None();
    Option<IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static CreateDefaultClientSupplierInput CreateDefaultClientSupplierInput(
      software.amazon.cryptography.materialProviders.model.CreateDefaultClientSupplierInput nativeValue) {
    return new CreateDefaultClientSupplierInput();
  }

  public static DecryptMaterialsInput DecryptMaterialsInput(
      software.amazon.cryptography.materialProviders.model.DecryptMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    return new DecryptMaterialsInput(algorithmSuiteId, commitmentPolicy, encryptedDataKeys, encryptionContext);
  }

  public static CreateRawAesKeyringInput CreateRawAesKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateRawAesKeyringInput nativeValue) {
    DafnySequence<? extends Character> keyNamespace;
    keyNamespace = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.keyNamespace());
    DafnySequence<? extends Character> keyName;
    keyName = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.keyName());
    DafnySequence<? extends Byte> wrappingKey;
    wrappingKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.wrappingKey());
    AesWrappingAlg wrappingAlg;
    wrappingAlg = ToDafny.AesWrappingAlg(nativeValue.wrappingAlg());
    return new CreateRawAesKeyringInput(keyNamespace, keyName, wrappingKey, wrappingAlg);
  }

  public static DafnySequence<? extends Byte> GetAlgorithmSuiteInfoInput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> binaryId;
    binaryId = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return binaryId;
  }

  public static CreateMultiKeyringInput CreateMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateMultiKeyringInput nativeValue) {
    Option<IKeyring> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(ToDafny.Keyring(nativeValue.generator()))
        : Option.create_None();
    DafnySequence<? extends IKeyring> childKeyrings;
    childKeyrings = ToDafny.KeyringList(nativeValue.childKeyrings());
    return new CreateMultiKeyringInput(generator, childKeyrings);
  }

  public static ECDSA ECDSA(
      software.amazon.cryptography.materialProviders.model.ECDSA nativeValue) {
    ECDSASignatureAlgorithm curve;
    curve = software.amazon.cryptography.primitives.ToDafny.ECDSASignatureAlgorithm(nativeValue.curve());
    return new ECDSA(curve);
  }

  public static ValidDecryptionMaterialsTransitionInput ValidDecryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialProviders.model.ValidDecryptionMaterialsTransitionInput nativeValue) {
    DecryptionMaterials start;
    start = ToDafny.DecryptionMaterials(nativeValue.start());
    DecryptionMaterials stop;
    stop = ToDafny.DecryptionMaterials(nativeValue.stop());
    return new ValidDecryptionMaterialsTransitionInput(start, stop);
  }

  public static Error Error(InvalidDecryptionMaterials nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidDecryptionMaterials(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfo nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfo(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfoOnEncrypt nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfoOnEncrypt(message);
  }

  public static Error Error(InvalidEncryptionMaterials nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidEncryptionMaterials(message);
  }

  public static Error Error(InvalidDecryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidDecryptionMaterialsTransition(message);
  }

  public static Error Error(InvalidEncryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidEncryptionMaterialsTransition(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfoOnDecrypt nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfoOnDecrypt(message);
  }

  public static Error Error(AwsCryptographicMaterialProvidersException nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_AwsCryptographicMaterialProvidersException(message);
  }

  public static AesWrappingAlg AesWrappingAlg(
      software.amazon.cryptography.materialProviders.model.AesWrappingAlg nativeValue) {
    switch (nativeValue) {
      case ALG_AES128_GCM_IV12_TAG16: {
        return AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
      }
      case ALG_AES192_GCM_IV12_TAG16: {
        return AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
      }
      case ALG_AES256_GCM_IV12_TAG16: {
        return AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.AesWrappingAlg.");
      }
    }
  }

  public static ESDKCommitmentPolicy ESDKCommitmentPolicy(
      software.amazon.cryptography.materialProviders.model.ESDKCommitmentPolicy nativeValue) {
    switch (nativeValue) {
      case FORBID_ENCRYPT_ALLOW_DECRYPT: {
        return ESDKCommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT();
      }
      case REQUIRE_ENCRYPT_ALLOW_DECRYPT: {
        return ESDKCommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
      }
      case REQUIRE_ENCRYPT_REQUIRE_DECRYPT: {
        return ESDKCommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKCommitmentPolicy.");
      }
    }
  }

  public static ESDKAlgorithmSuiteId ESDKAlgorithmSuiteId(
      software.amazon.cryptography.materialProviders.model.ESDKAlgorithmSuiteId nativeValue) {
    switch (nativeValue) {
      case ALG_AES_128_GCM_IV12_TAG16_NO_KDF: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
      }
      case ALG_AES_192_GCM_IV12_TAG16_NO_KDF: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
      }
      case ALG_AES_256_GCM_IV12_TAG16_NO_KDF: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
      }
      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
      }
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
      }
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
      }
      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
      }
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
      }
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
      }
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY();
      }
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: {
        return ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKAlgorithmSuiteId.");
      }
    }
  }

  public static PaddingScheme PaddingScheme(
      software.amazon.cryptography.materialProviders.model.PaddingScheme nativeValue) {
    switch (nativeValue) {
      case PKCS1: {
        return PaddingScheme.create_PKCS1();
      }
      case OAEP_SHA1_MGF1: {
        return PaddingScheme.create_OAEP__SHA1__MGF1();
      }
      case OAEP_SHA256_MGF1: {
        return PaddingScheme.create_OAEP__SHA256__MGF1();
      }
      case OAEP_SHA384_MGF1: {
        return PaddingScheme.create_OAEP__SHA384__MGF1();
      }
      case OAEP_SHA512_MGF1: {
        return PaddingScheme.create_OAEP__SHA512__MGF1();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.PaddingScheme.");
      }
    }
  }

  public static SignatureAlgorithm SignatureAlgorithm(
      software.amazon.cryptography.materialProviders.model.SignatureAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.ECDSA())) {
      return SignatureAlgorithm.create_ECDSA(ToDafny.ECDSA(nativeValue.ECDSA()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return SignatureAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.SignatureAlgorithm.");
  }

  public static Encrypt Encrypt(
      software.amazon.cryptography.materialProviders.model.Encrypt nativeValue) {
    return Encrypt.create(software.amazon.cryptography.primitives.ToDafny.AES_GCM(nativeValue.AES_GCM()));
  }

  public static AlgorithmSuiteId AlgorithmSuiteId(
      software.amazon.cryptography.materialProviders.model.AlgorithmSuiteId nativeValue) {
    if (Objects.nonNull(nativeValue.ESDK())) {
      return AlgorithmSuiteId.create_ESDK(ToDafny.ESDKAlgorithmSuiteId(nativeValue.ESDK()));
    }
    if (Objects.nonNull(nativeValue.DBE())) {
      return AlgorithmSuiteId.create_DBE(ToDafny.DBEAlgorithmSuiteId(nativeValue.DBE()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteId.");
  }

  public static DerivationAlgorithm DerivationAlgorithm(
      software.amazon.cryptography.materialProviders.model.DerivationAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.HKDF())) {
      return DerivationAlgorithm.create_HKDF(ToDafny.HKDF(nativeValue.HKDF()));
    }
    if (Objects.nonNull(nativeValue.IDENTITY())) {
      return DerivationAlgorithm.create_IDENTITY(ToDafny.IDENTITY(nativeValue.IDENTITY()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return DerivationAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.DerivationAlgorithm.");
  }

  public static CommitmentPolicy CommitmentPolicy(
      software.amazon.cryptography.materialProviders.model.CommitmentPolicy nativeValue) {
    if (Objects.nonNull(nativeValue.ESDK())) {
      return CommitmentPolicy.create_ESDK(ToDafny.ESDKCommitmentPolicy(nativeValue.ESDK()));
    }
    if (Objects.nonNull(nativeValue.DBE())) {
      return CommitmentPolicy.create_DBE(ToDafny.DBECommitmentPolicy(nativeValue.DBE()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.CommitmentPolicy.");
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> AccountIdList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> GrantTokenList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> KmsKeyIdList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends EncryptedDataKey> EncryptedDataKeyList(
      List<software.amazon.cryptography.materialProviders.model.EncryptedDataKey> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.cryptography.materialProviders.ToDafny::EncryptedDataKey, 
        EncryptedDataKey._typeDescriptor());
  }

   public static <I extends software.amazon.cryptography.materialProviders.IKeyring> DafnySequence<? extends IKeyring> KeyringList(
          List<I> nativeValue
  ) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.cryptography.materialProviders.ToDafny::Keyring, 
        TypeDescriptor.reference(IKeyring.class));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> RegionList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> EncryptionContext(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes);
  }

  public static ICryptographicMaterialsManager CryptographicMaterialsManager(
          software.amazon.cryptography.materialProviders.ICryptographicMaterialsManager nativeValue
  ) {
    return CryptographicMaterialsManager.create(nativeValue).impl();
  }

  public static IKeyring Keyring(
          software.amazon.cryptography.materialProviders.IKeyring nativeValue
  ) {
    return Keyring.create(nativeValue).impl();
  }

  public static IClientSupplier ClientSupplier(
          software.amazon.cryptography.materialProviders.IClientSupplier nativeValue
  ) {
    return ClientSupplier.create(nativeValue).impl();
  }

    public static SymmetricSignatureAlgorithm SymmetricSignatureAlgorithm(
      software.amazon.cryptography.materialProviders.model.SymmetricSignatureAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.HMAC())) {
      return SymmetricSignatureAlgorithm.create_HMAC(software.amazon.cryptography.primitives.ToDafny.DigestAlgorithm(nativeValue.HMAC()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return SymmetricSignatureAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.SymmetricSignatureAlgorithm.");
  }

  public static EdkWrappingAlgorithm EdkWrappingAlgorithm(
      software.amazon.cryptography.materialProviders.model.EdkWrappingAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.DIRECT_KEY_WRAPPING())) {
      return EdkWrappingAlgorithm.create_DIRECT__KEY__WRAPPING(ToDafny.DIRECT_KEY_WRAPPING(nativeValue.DIRECT_KEY_WRAPPING()));
    }
    if (Objects.nonNull(nativeValue.IntermediateKeyWrapping())) {
      return EdkWrappingAlgorithm.create_IntermediateKeyWrapping(ToDafny.IntermediateKeyWrapping(nativeValue.IntermediateKeyWrapping()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.EdkWrappingAlgorithm.");
  }

  public static DIRECT__KEY__WRAPPING DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING nativeValue) {
    return new DIRECT__KEY__WRAPPING();
  }

  public static DBEAlgorithmSuiteId DBEAlgorithmSuiteId(
      software.amazon.cryptography.materialProviders.model.DBEAlgorithmSuiteId nativeValue) {
    switch (nativeValue) {
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384: {
        return DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384();
      }
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384: {
        return DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.DBEAlgorithmSuiteId.");
      }
    }
  }

  public static IntermediateKeyWrapping IntermediateKeyWrapping(
      software.amazon.cryptography.materialProviders.model.IntermediateKeyWrapping nativeValue) {
    DerivationAlgorithm keyEncryptionKeyKdf;
    keyEncryptionKeyKdf = ToDafny.DerivationAlgorithm(nativeValue.keyEncryptionKeyKdf());
    DerivationAlgorithm macKeyKdf;
    macKeyKdf = ToDafny.DerivationAlgorithm(nativeValue.macKeyKdf());
    Encrypt pdkEncryptAlgorithm;
    pdkEncryptAlgorithm = ToDafny.Encrypt(nativeValue.pdkEncryptAlgorithm());
    return new IntermediateKeyWrapping(keyEncryptionKeyKdf, macKeyKdf, pdkEncryptAlgorithm);
  }

  public static DBECommitmentPolicy DBECommitmentPolicy(
      software.amazon.cryptography.materialProviders.model.DBECommitmentPolicy nativeValue) {
    switch (nativeValue) {
      case REQUIRE_ENCRYPT_REQUIRE_DECRYPT: {
        return DBECommitmentPolicy.create(); // TODO Dafny converts datatypes with a single constructor in a different way than expected
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.DBECommitmentPolicy.");
      }
    }
  }
}
