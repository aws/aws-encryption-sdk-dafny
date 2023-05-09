// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

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
import software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient;
import software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg;
import software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.internaldafny.types.BeaconKeyMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.BranchKeyMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateCryptographicMaterialsCacheInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateExpectedEncryptionContextCMMInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.internaldafny.types.DBECommitmentPolicy;
import software.amazon.cryptography.materialproviders.internaldafny.types.DIRECT__KEY__WRAPPING;
import software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.DerivationAlgorithm;
import software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter;
import software.amazon.cryptography.materialproviders.internaldafny.types.ECDSA;
import software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.internaldafny.types.ESDKCommitmentPolicy;
import software.amazon.cryptography.materialproviders.internaldafny.types.EdkWrappingAlgorithm;
import software.amazon.cryptography.materialproviders.internaldafny.types.Encrypt;
import software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey;
import software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_EntryAlreadyExists;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_EntryDoesNotExist;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidDecryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidEncryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.HKDF;
import software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient;
import software.amazon.cryptography.materialproviders.internaldafny.types.IDENTITY;
import software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.IntermediateKeyWrapping;
import software.amazon.cryptography.materialproviders.internaldafny.types.MaterialProvidersConfig;
import software.amazon.cryptography.materialproviders.internaldafny.types.Materials;
import software.amazon.cryptography.materialproviders.internaldafny.types.None;
import software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput;
import software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme;
import software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.SignatureAlgorithm;
import software.amazon.cryptography.materialproviders.internaldafny.types.SymmetricSignatureAlgorithm;
import software.amazon.cryptography.materialproviders.internaldafny.types.UpdaterUsageMetadataInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnEncryptInput;
import software.amazon.cryptography.materialproviders.model.AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialproviders.model.CollectionOfErrors;
import software.amazon.cryptography.materialproviders.model.DIRECT_KEY_WRAPPING;
import software.amazon.cryptography.materialproviders.model.EntryAlreadyExists;
import software.amazon.cryptography.materialproviders.model.EntryDoesNotExist;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialproviders.model.InvalidDecryptionMaterials;
import software.amazon.cryptography.materialproviders.model.InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.model.InvalidEncryptionMaterials;
import software.amazon.cryptography.materialproviders.model.InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.model.OpaqueError;
import software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm;
import software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec;
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;

public class ToDafny {
  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof AwsCryptographicMaterialProvidersException) {
      return ToDafny.Error((AwsCryptographicMaterialProvidersException) nativeValue);
    }
    if (nativeValue instanceof EntryAlreadyExists) {
      return ToDafny.Error((EntryAlreadyExists) nativeValue);
    }
    if (nativeValue instanceof EntryDoesNotExist) {
      return ToDafny.Error((EntryDoesNotExist) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfo) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfo) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnDecrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnDecrypt) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnEncrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnEncrypt) nativeValue);
    }
    if (nativeValue instanceof InvalidDecryptionMaterials) {
      return ToDafny.Error((InvalidDecryptionMaterials) nativeValue);
    }
    if (nativeValue instanceof InvalidDecryptionMaterialsTransition) {
      return ToDafny.Error((InvalidDecryptionMaterialsTransition) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterials) {
      return ToDafny.Error((InvalidEncryptionMaterials) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterialsTransition) {
      return ToDafny.Error((InvalidEncryptionMaterialsTransition) nativeValue);
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
    return Error.create_CollectionOfErrors(list);
  }

  public static AlgorithmSuiteInfo AlgorithmSuiteInfo(
      software.amazon.cryptography.materialproviders.model.AlgorithmSuiteInfo nativeValue) {
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

  public static BeaconKeyMaterials BeaconKeyMaterials(
      software.amazon.cryptography.materialproviders.model.BeaconKeyMaterials nativeValue) {
    DafnySequence<? extends Character> beaconKeyIdentifier;
    beaconKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.beaconKeyIdentifier());
    Option<DafnySequence<? extends Byte>> beaconKey;
    beaconKey = Objects.nonNull(nativeValue.beaconKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.beaconKey()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Byte>>> hmacKeys;
    hmacKeys = (Objects.nonNull(nativeValue.hmacKeys()) && nativeValue.hmacKeys().size() > 0) ?
        Option.create_Some(ToDafny.HmacKeyMap(nativeValue.hmacKeys()))
        : Option.create_None();
    return new BeaconKeyMaterials(beaconKeyIdentifier, beaconKey, hmacKeys);
  }

  public static BranchKeyMaterials BranchKeyMaterials(
      software.amazon.cryptography.materialproviders.model.BranchKeyMaterials nativeValue) {
    DafnySequence<? extends Byte> branchKeyVersion;
    branchKeyVersion = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.branchKeyVersion());
    DafnySequence<? extends Byte> branchKey;
    branchKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.branchKey());
    return new BranchKeyMaterials(branchKeyVersion, branchKey);
  }

  public static CreateAwsKmsDiscoveryKeyringInput CreateAwsKmsDiscoveryKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryKeyringInput nativeValue) {
    IKMSClient kmsClient;
    kmsClient = software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(nativeValue.kmsClient());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsDiscoveryKeyringInput(kmsClient, discoveryFilter, grantTokens);
  }

  public static CreateAwsKmsDiscoveryMultiKeyringInput CreateAwsKmsDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsHierarchicalKeyringInput CreateAwsKmsHierarchicalKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsHierarchicalKeyringInput nativeValue) {
    Option<DafnySequence<? extends Character>> branchKeyId;
    branchKeyId = Objects.nonNull(nativeValue.branchKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyId()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier> branchKeyIdSupplier;
    branchKeyIdSupplier = Objects.nonNull(nativeValue.branchKeyIdSupplier()) ?
        Option.create_Some(ToDafny.BranchKeyIdSupplier(nativeValue.branchKeyIdSupplier()))
        : Option.create_None();
    IKeyStoreClient keyStore;
    keyStore = software.amazon.cryptography.keystore.ToDafny.KeyStore(nativeValue.keyStore());
    Long ttlSeconds;
    ttlSeconds = (nativeValue.ttlSeconds());
    Option<Integer> maxCacheSize;
    maxCacheSize = Objects.nonNull(nativeValue.maxCacheSize()) ?
        Option.create_Some((nativeValue.maxCacheSize()))
        : Option.create_None();
    return new CreateAwsKmsHierarchicalKeyringInput(branchKeyId, branchKeyIdSupplier, keyStore, ttlSeconds, maxCacheSize);
  }

  public static CreateAwsKmsKeyringInput CreateAwsKmsKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKMSClient kmsClient;
    kmsClient = software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(nativeValue.kmsClient());
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsKeyringInput(kmsKeyId, kmsClient, grantTokens);
  }

  public static CreateAwsKmsMrkDiscoveryKeyringInput CreateAwsKmsMrkDiscoveryKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryKeyringInput nativeValue) {
    IKMSClient kmsClient;
    kmsClient = software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(nativeValue.kmsClient());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    DafnySequence<? extends Character> region;
    region = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.region());
    return new CreateAwsKmsMrkDiscoveryKeyringInput(kmsClient, discoveryFilter, grantTokens, region);
  }

  public static CreateAwsKmsMrkDiscoveryMultiKeyringInput CreateAwsKmsMrkDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsMrkKeyringInput CreateAwsKmsMrkKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKMSClient kmsClient;
    kmsClient = software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(nativeValue.kmsClient());
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkKeyringInput(kmsKeyId, kmsClient, grantTokens);
  }

  public static CreateAwsKmsMrkMultiKeyringInput CreateAwsKmsMrkMultiKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkMultiKeyringInput nativeValue) {
    Option<DafnySequence<? extends Character>> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.generator()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> kmsKeyIds;
    kmsKeyIds = (Objects.nonNull(nativeValue.kmsKeyIds()) && nativeValue.kmsKeyIds().size() > 0) ?
        Option.create_Some(ToDafny.KmsKeyIdList(nativeValue.kmsKeyIds()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsMultiKeyringInput CreateAwsKmsMultiKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsMultiKeyringInput nativeValue) {
    Option<DafnySequence<? extends Character>> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.generator()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> kmsKeyIds;
    kmsKeyIds = (Objects.nonNull(nativeValue.kmsKeyIds()) && nativeValue.kmsKeyIds().size() > 0) ?
        Option.create_Some(ToDafny.KmsKeyIdList(nativeValue.kmsKeyIds()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static CreateAwsKmsRsaKeyringInput CreateAwsKmsRsaKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateAwsKmsRsaKeyringInput nativeValue) {
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.publicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.publicKey()))
        : Option.create_None();
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    EncryptionAlgorithmSpec encryptionAlgorithm;
    encryptionAlgorithm = software.amazon.cryptography.services.kms.internaldafny.ToDafny.EncryptionAlgorithmSpec(nativeValue.encryptionAlgorithm());
    Option<IKMSClient> kmsClient;
    kmsClient = Objects.nonNull(nativeValue.kmsClient()) ?
        Option.create_Some(software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(nativeValue.kmsClient()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsRsaKeyringInput(publicKey, kmsKeyId, encryptionAlgorithm, kmsClient, grantTokens);
  }

  public static CreateCryptographicMaterialsCacheInput CreateCryptographicMaterialsCacheInput(
      software.amazon.cryptography.materialproviders.model.CreateCryptographicMaterialsCacheInput nativeValue) {
    Integer entryCapacity;
    entryCapacity = (nativeValue.entryCapacity());
    Option<Integer> entryPruningTailSize;
    entryPruningTailSize = Objects.nonNull(nativeValue.entryPruningTailSize()) ?
        Option.create_Some((nativeValue.entryPruningTailSize()))
        : Option.create_None();
    return new CreateCryptographicMaterialsCacheInput(entryCapacity, entryPruningTailSize);
  }

  public static CreateDefaultClientSupplierInput CreateDefaultClientSupplierInput(
      software.amazon.cryptography.materialproviders.model.CreateDefaultClientSupplierInput nativeValue) {
    return new CreateDefaultClientSupplierInput();
  }

  public static CreateDefaultCryptographicMaterialsManagerInput CreateDefaultCryptographicMaterialsManagerInput(
      software.amazon.cryptography.materialproviders.model.CreateDefaultCryptographicMaterialsManagerInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring;
    keyring = ToDafny.Keyring(nativeValue.keyring());
    return new CreateDefaultCryptographicMaterialsManagerInput(keyring);
  }

  public static CreateExpectedEncryptionContextCMMInput CreateExpectedEncryptionContextCMMInput(
      software.amazon.cryptography.materialproviders.model.CreateExpectedEncryptionContextCMMInput nativeValue) {
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager> underlyingCMM;
    underlyingCMM = Objects.nonNull(nativeValue.underlyingCMM()) ?
        Option.create_Some(ToDafny.CryptographicMaterialsManager(nativeValue.underlyingCMM()))
        : Option.create_None();
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> keyring;
    keyring = Objects.nonNull(nativeValue.keyring()) ?
        Option.create_Some(ToDafny.Keyring(nativeValue.keyring()))
        : Option.create_None();
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    return new CreateExpectedEncryptionContextCMMInput(underlyingCMM, keyring, requiredEncryptionContextKeys);
  }

  public static CreateMultiKeyringInput CreateMultiKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateMultiKeyringInput nativeValue) {
    Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(ToDafny.Keyring(nativeValue.generator()))
        : Option.create_None();
    DafnySequence<? extends software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> childKeyrings;
    childKeyrings = ToDafny.KeyringList(nativeValue.childKeyrings());
    return new CreateMultiKeyringInput(generator, childKeyrings);
  }

  public static CreateRawAesKeyringInput CreateRawAesKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateRawAesKeyringInput nativeValue) {
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

  public static CreateRawRsaKeyringInput CreateRawRsaKeyringInput(
      software.amazon.cryptography.materialproviders.model.CreateRawRsaKeyringInput nativeValue) {
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

  public static DecryptionMaterials DecryptionMaterials(
      software.amazon.cryptography.materialproviders.model.DecryptionMaterials nativeValue) {
    AlgorithmSuiteInfo algorithmSuite;
    algorithmSuite = ToDafny.AlgorithmSuiteInfo(nativeValue.algorithmSuite());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    Option<DafnySequence<? extends Byte>> plaintextDataKey;
    plaintextDataKey = Objects.nonNull(nativeValue.plaintextDataKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.plaintextDataKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> verificationKey;
    verificationKey = Objects.nonNull(nativeValue.verificationKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> symmetricSigningKey;
    symmetricSigningKey = Objects.nonNull(nativeValue.symmetricSigningKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.symmetricSigningKey()))
        : Option.create_None();
    return new DecryptionMaterials(algorithmSuite, encryptionContext, requiredEncryptionContextKeys, plaintextDataKey, verificationKey, symmetricSigningKey);
  }

  public static DecryptMaterialsInput DecryptMaterialsInput(
      software.amazon.cryptography.materialproviders.model.DecryptMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    Option<DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>>> reproducedEncryptionContext;
    reproducedEncryptionContext = (Objects.nonNull(nativeValue.reproducedEncryptionContext()) && nativeValue.reproducedEncryptionContext().size() > 0) ?
        Option.create_Some(ToDafny.EncryptionContext(nativeValue.reproducedEncryptionContext()))
        : Option.create_None();
    return new DecryptMaterialsInput(algorithmSuiteId, commitmentPolicy, encryptedDataKeys, encryptionContext, reproducedEncryptionContext);
  }

  public static DecryptMaterialsOutput DecryptMaterialsOutput(
      software.amazon.cryptography.materialproviders.model.DecryptMaterialsOutput nativeValue) {
    DecryptionMaterials decryptionMaterials;
    decryptionMaterials = ToDafny.DecryptionMaterials(nativeValue.decryptionMaterials());
    return new DecryptMaterialsOutput(decryptionMaterials);
  }

  public static DeleteCacheEntryInput DeleteCacheEntryInput(
      software.amazon.cryptography.materialproviders.model.DeleteCacheEntryInput nativeValue) {
    DafnySequence<? extends Byte> identifier;
    identifier = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.identifier());
    return new DeleteCacheEntryInput(identifier);
  }

  public static DIRECT__KEY__WRAPPING DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING nativeValue) {
    return new DIRECT__KEY__WRAPPING();
  }

  public static DiscoveryFilter DiscoveryFilter(
      software.amazon.cryptography.materialproviders.model.DiscoveryFilter nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> accountIds;
    accountIds = ToDafny.AccountIdList(nativeValue.accountIds());
    DafnySequence<? extends Character> partition;
    partition = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.partition());
    return new DiscoveryFilter(accountIds, partition);
  }

  public static ECDSA ECDSA(
      software.amazon.cryptography.materialproviders.model.ECDSA nativeValue) {
    ECDSASignatureAlgorithm curve;
    curve = software.amazon.cryptography.primitives.ToDafny.ECDSASignatureAlgorithm(nativeValue.curve());
    return new ECDSA(curve);
  }

  public static EncryptedDataKey EncryptedDataKey(
      software.amazon.cryptography.materialproviders.model.EncryptedDataKey nativeValue) {
    DafnySequence<? extends Byte> keyProviderId;
    keyProviderId = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.keyProviderId());
    DafnySequence<? extends Byte> keyProviderInfo;
    keyProviderInfo = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.keyProviderInfo());
    DafnySequence<? extends Byte> ciphertext;
    ciphertext = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ciphertext());
    return new EncryptedDataKey(keyProviderId, keyProviderInfo, ciphertext);
  }

  public static EncryptionMaterials EncryptionMaterials(
      software.amazon.cryptography.materialproviders.model.EncryptionMaterials nativeValue) {
    AlgorithmSuiteInfo algorithmSuite;
    algorithmSuite = ToDafny.AlgorithmSuiteInfo(nativeValue.algorithmSuite());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    Option<DafnySequence<? extends Byte>> plaintextDataKey;
    plaintextDataKey = Objects.nonNull(nativeValue.plaintextDataKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.plaintextDataKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> signingKey;
    signingKey = Objects.nonNull(nativeValue.signingKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Byte>>> symmetricSigningKeys;
    symmetricSigningKeys = (Objects.nonNull(nativeValue.symmetricSigningKeys()) && nativeValue.symmetricSigningKeys().size() > 0) ?
        Option.create_Some(ToDafny.SymmetricSigningKeyList(nativeValue.symmetricSigningKeys()))
        : Option.create_None();
    return new EncryptionMaterials(algorithmSuite, encryptionContext, encryptedDataKeys, requiredEncryptionContextKeys, plaintextDataKey, signingKey, symmetricSigningKeys);
  }

  public static DafnySequence<? extends Byte> GetAlgorithmSuiteInfoInput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> binaryId;
    binaryId = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return binaryId;
  }

  public static GetBranchKeyIdInput GetBranchKeyIdInput(
      software.amazon.cryptography.materialproviders.model.GetBranchKeyIdInput nativeValue) {
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    return new GetBranchKeyIdInput(encryptionContext);
  }

  public static GetBranchKeyIdOutput GetBranchKeyIdOutput(
      software.amazon.cryptography.materialproviders.model.GetBranchKeyIdOutput nativeValue) {
    DafnySequence<? extends Character> branchKeyId;
    branchKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyId());
    return new GetBranchKeyIdOutput(branchKeyId);
  }

  public static GetCacheEntryInput GetCacheEntryInput(
      software.amazon.cryptography.materialproviders.model.GetCacheEntryInput nativeValue) {
    DafnySequence<? extends Byte> identifier;
    identifier = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.identifier());
    Option<Long> bytesUsed;
    bytesUsed = Objects.nonNull(nativeValue.bytesUsed()) ?
        Option.create_Some((nativeValue.bytesUsed()))
        : Option.create_None();
    return new GetCacheEntryInput(identifier, bytesUsed);
  }

  public static GetCacheEntryOutput GetCacheEntryOutput(
      software.amazon.cryptography.materialproviders.model.GetCacheEntryOutput nativeValue) {
    Materials materials;
    materials = ToDafny.Materials(nativeValue.materials());
    Long creationTime;
    creationTime = (nativeValue.creationTime());
    Long expiryTime;
    expiryTime = (nativeValue.expiryTime());
    Integer messagesUsed;
    messagesUsed = (nativeValue.messagesUsed());
    Integer bytesUsed;
    bytesUsed = (nativeValue.bytesUsed());
    return new GetCacheEntryOutput(materials, creationTime, expiryTime, messagesUsed, bytesUsed);
  }

  public static GetClientInput GetClientInput(
      software.amazon.cryptography.materialproviders.model.GetClientInput nativeValue) {
    DafnySequence<? extends Character> region;
    region = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.region());
    return new GetClientInput(region);
  }

  public static GetEncryptionMaterialsInput GetEncryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsInput nativeValue) {
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
    Option<DafnySequence<? extends DafnySequence<? extends Byte>>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = (Objects.nonNull(nativeValue.requiredEncryptionContextKeys()) && nativeValue.requiredEncryptionContextKeys().size() > 0) ?
        Option.create_Some(ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys()))
        : Option.create_None();
    return new GetEncryptionMaterialsInput(encryptionContext, commitmentPolicy, algorithmSuiteId, maxPlaintextLength, requiredEncryptionContextKeys);
  }

  public static GetEncryptionMaterialsOutput GetEncryptionMaterialsOutput(
      software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsOutput nativeValue) {
    EncryptionMaterials encryptionMaterials;
    encryptionMaterials = ToDafny.EncryptionMaterials(nativeValue.encryptionMaterials());
    return new GetEncryptionMaterialsOutput(encryptionMaterials);
  }

  public static HKDF HKDF(software.amazon.cryptography.materialproviders.model.HKDF nativeValue) {
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

  public static IDENTITY IDENTITY(
      software.amazon.cryptography.materialproviders.model.IDENTITY nativeValue) {
    return new IDENTITY();
  }

  public static InitializeDecryptionMaterialsInput InitializeDecryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.model.InitializeDecryptionMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    return new InitializeDecryptionMaterialsInput(algorithmSuiteId, encryptionContext, requiredEncryptionContextKeys);
  }

  public static InitializeEncryptionMaterialsInput InitializeEncryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.model.InitializeEncryptionMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    Option<DafnySequence<? extends Byte>> signingKey;
    signingKey = Objects.nonNull(nativeValue.signingKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> verificationKey;
    verificationKey = Objects.nonNull(nativeValue.verificationKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey()))
        : Option.create_None();
    return new InitializeEncryptionMaterialsInput(algorithmSuiteId, encryptionContext, requiredEncryptionContextKeys, signingKey, verificationKey);
  }

  public static IntermediateKeyWrapping IntermediateKeyWrapping(
      software.amazon.cryptography.materialproviders.model.IntermediateKeyWrapping nativeValue) {
    DerivationAlgorithm keyEncryptionKeyKdf;
    keyEncryptionKeyKdf = ToDafny.DerivationAlgorithm(nativeValue.keyEncryptionKeyKdf());
    DerivationAlgorithm macKeyKdf;
    macKeyKdf = ToDafny.DerivationAlgorithm(nativeValue.macKeyKdf());
    Encrypt pdkEncryptAlgorithm;
    pdkEncryptAlgorithm = ToDafny.Encrypt(nativeValue.pdkEncryptAlgorithm());
    return new IntermediateKeyWrapping(keyEncryptionKeyKdf, macKeyKdf, pdkEncryptAlgorithm);
  }

  public static MaterialProvidersConfig MaterialProvidersConfig(
      software.amazon.cryptography.materialproviders.model.MaterialProvidersConfig nativeValue) {
    return new MaterialProvidersConfig();
  }

  public static None None(software.amazon.cryptography.materialproviders.model.None nativeValue) {
    return new None();
  }

  public static OnDecryptInput OnDecryptInput(
      software.amazon.cryptography.materialproviders.model.OnDecryptInput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    return new OnDecryptInput(materials, encryptedDataKeys);
  }

  public static OnDecryptOutput OnDecryptOutput(
      software.amazon.cryptography.materialproviders.model.OnDecryptOutput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    return new OnDecryptOutput(materials);
  }

  public static OnEncryptInput OnEncryptInput(
      software.amazon.cryptography.materialproviders.model.OnEncryptInput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptInput(materials);
  }

  public static OnEncryptOutput OnEncryptOutput(
      software.amazon.cryptography.materialproviders.model.OnEncryptOutput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptOutput(materials);
  }

  public static PutCacheEntryInput PutCacheEntryInput(
      software.amazon.cryptography.materialproviders.model.PutCacheEntryInput nativeValue) {
    DafnySequence<? extends Byte> identifier;
    identifier = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.identifier());
    Materials materials;
    materials = ToDafny.Materials(nativeValue.materials());
    Long creationTime;
    creationTime = (nativeValue.creationTime());
    Long expiryTime;
    expiryTime = (nativeValue.expiryTime());
    Option<Integer> messagesUsed;
    messagesUsed = Objects.nonNull(nativeValue.messagesUsed()) ?
        Option.create_Some((nativeValue.messagesUsed()))
        : Option.create_None();
    Option<Integer> bytesUsed;
    bytesUsed = Objects.nonNull(nativeValue.bytesUsed()) ?
        Option.create_Some((nativeValue.bytesUsed()))
        : Option.create_None();
    return new PutCacheEntryInput(identifier, materials, creationTime, expiryTime, messagesUsed, bytesUsed);
  }

  public static UpdaterUsageMetadataInput UpdaterUsageMetadataInput(
      software.amazon.cryptography.materialproviders.model.UpdaterUsageMetadataInput nativeValue) {
    DafnySequence<? extends Byte> identifier;
    identifier = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.identifier());
    Integer bytesUsed;
    bytesUsed = (nativeValue.bytesUsed());
    return new UpdaterUsageMetadataInput(identifier, bytesUsed);
  }

  public static ValidateCommitmentPolicyOnDecryptInput ValidateCommitmentPolicyOnDecryptInput(
      software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnDecryptInput nativeValue) {
    AlgorithmSuiteId algorithm;
    algorithm = ToDafny.AlgorithmSuiteId(nativeValue.algorithm());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    return new ValidateCommitmentPolicyOnDecryptInput(algorithm, commitmentPolicy);
  }

  public static ValidateCommitmentPolicyOnEncryptInput ValidateCommitmentPolicyOnEncryptInput(
      software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnEncryptInput nativeValue) {
    AlgorithmSuiteId algorithm;
    algorithm = ToDafny.AlgorithmSuiteId(nativeValue.algorithm());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    return new ValidateCommitmentPolicyOnEncryptInput(algorithm, commitmentPolicy);
  }

  public static ValidDecryptionMaterialsTransitionInput ValidDecryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialproviders.model.ValidDecryptionMaterialsTransitionInput nativeValue) {
    DecryptionMaterials start;
    start = ToDafny.DecryptionMaterials(nativeValue.start());
    DecryptionMaterials stop;
    stop = ToDafny.DecryptionMaterials(nativeValue.stop());
    return new ValidDecryptionMaterialsTransitionInput(start, stop);
  }

  public static ValidEncryptionMaterialsTransitionInput ValidEncryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialproviders.model.ValidEncryptionMaterialsTransitionInput nativeValue) {
    EncryptionMaterials start;
    start = ToDafny.EncryptionMaterials(nativeValue.start());
    EncryptionMaterials stop;
    stop = ToDafny.EncryptionMaterials(nativeValue.stop());
    return new ValidEncryptionMaterialsTransitionInput(start, stop);
  }

  public static Error Error(AwsCryptographicMaterialProvidersException nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_AwsCryptographicMaterialProvidersException(message);
  }

  public static Error Error(EntryAlreadyExists nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_EntryAlreadyExists(message);
  }

  public static Error Error(EntryDoesNotExist nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_EntryDoesNotExist(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfo nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfo(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfoOnDecrypt nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfoOnDecrypt(message);
  }

  public static Error Error(InvalidAlgorithmSuiteInfoOnEncrypt nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfoOnEncrypt(message);
  }

  public static Error Error(InvalidDecryptionMaterials nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidDecryptionMaterials(message);
  }

  public static Error Error(InvalidDecryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidDecryptionMaterialsTransition(message);
  }

  public static Error Error(InvalidEncryptionMaterials nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidEncryptionMaterials(message);
  }

  public static Error Error(InvalidEncryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidEncryptionMaterialsTransition(message);
  }

  public static AesWrappingAlg AesWrappingAlg(
      software.amazon.cryptography.materialproviders.model.AesWrappingAlg nativeValue) {
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
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.");
      }
    }
  }

  public static DBEAlgorithmSuiteId DBEAlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.model.DBEAlgorithmSuiteId nativeValue) {
    switch (nativeValue) {
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384: {
        return DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384();
      }
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384: {
        return DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.");
      }
    }
  }

  public static DBECommitmentPolicy DBECommitmentPolicy(
      software.amazon.cryptography.materialproviders.model.DBECommitmentPolicy nativeValue) {
    switch (nativeValue) {
      case REQUIRE_ENCRYPT_REQUIRE_DECRYPT: {
        return DBECommitmentPolicy.create();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.DBECommitmentPolicy.");
      }
    }
  }

  public static ESDKAlgorithmSuiteId ESDKAlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.model.ESDKAlgorithmSuiteId nativeValue) {
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
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.");
      }
    }
  }

  public static ESDKCommitmentPolicy ESDKCommitmentPolicy(
      software.amazon.cryptography.materialproviders.model.ESDKCommitmentPolicy nativeValue) {
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
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.ESDKCommitmentPolicy.");
      }
    }
  }

  public static PaddingScheme PaddingScheme(
      software.amazon.cryptography.materialproviders.model.PaddingScheme nativeValue) {
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
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.");
      }
    }
  }

  public static AlgorithmSuiteId AlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.model.AlgorithmSuiteId nativeValue) {
    if (Objects.nonNull(nativeValue.ESDK())) {
      return AlgorithmSuiteId.create_ESDK(ToDafny.ESDKAlgorithmSuiteId(nativeValue.ESDK()));
    }
    if (Objects.nonNull(nativeValue.DBE())) {
      return AlgorithmSuiteId.create_DBE(ToDafny.DBEAlgorithmSuiteId(nativeValue.DBE()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.");
  }

  public static CommitmentPolicy CommitmentPolicy(
      software.amazon.cryptography.materialproviders.model.CommitmentPolicy nativeValue) {
    if (Objects.nonNull(nativeValue.ESDK())) {
      return CommitmentPolicy.create_ESDK(ToDafny.ESDKCommitmentPolicy(nativeValue.ESDK()));
    }
    if (Objects.nonNull(nativeValue.DBE())) {
      return CommitmentPolicy.create_DBE(ToDafny.DBECommitmentPolicy(nativeValue.DBE()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.");
  }

  public static DerivationAlgorithm DerivationAlgorithm(
      software.amazon.cryptography.materialproviders.model.DerivationAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.HKDF())) {
      return DerivationAlgorithm.create_HKDF(ToDafny.HKDF(nativeValue.HKDF()));
    }
    if (Objects.nonNull(nativeValue.IDENTITY())) {
      return DerivationAlgorithm.create_IDENTITY(ToDafny.IDENTITY(nativeValue.IDENTITY()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return DerivationAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.DerivationAlgorithm.");
  }

  public static EdkWrappingAlgorithm EdkWrappingAlgorithm(
      software.amazon.cryptography.materialproviders.model.EdkWrappingAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.DIRECT_KEY_WRAPPING())) {
      return EdkWrappingAlgorithm.create_DIRECT__KEY__WRAPPING(ToDafny.DIRECT_KEY_WRAPPING(nativeValue.DIRECT_KEY_WRAPPING()));
    }
    if (Objects.nonNull(nativeValue.IntermediateKeyWrapping())) {
      return EdkWrappingAlgorithm.create_IntermediateKeyWrapping(ToDafny.IntermediateKeyWrapping(nativeValue.IntermediateKeyWrapping()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.EdkWrappingAlgorithm.");
  }

  public static Encrypt Encrypt(
      software.amazon.cryptography.materialproviders.model.Encrypt nativeValue) {
    if (Objects.nonNull(nativeValue.AES_GCM())) {
      return Encrypt.create(software.amazon.cryptography.primitives.ToDafny.AES_GCM(nativeValue.AES_GCM()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.Encrypt.");
  }

  public static Materials Materials(
      software.amazon.cryptography.materialproviders.model.Materials nativeValue) {
    if (Objects.nonNull(nativeValue.Encryption())) {
      return Materials.create_Encryption(ToDafny.EncryptionMaterials(nativeValue.Encryption()));
    }
    if (Objects.nonNull(nativeValue.Decryption())) {
      return Materials.create_Decryption(ToDafny.DecryptionMaterials(nativeValue.Decryption()));
    }
    if (Objects.nonNull(nativeValue.BranchKey())) {
      return Materials.create_BranchKey(ToDafny.BranchKeyMaterials(nativeValue.BranchKey()));
    }
    if (Objects.nonNull(nativeValue.BeaconKey())) {
      return Materials.create_BeaconKey(ToDafny.BeaconKeyMaterials(nativeValue.BeaconKey()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.Materials.");
  }

  public static SignatureAlgorithm SignatureAlgorithm(
      software.amazon.cryptography.materialproviders.model.SignatureAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.ECDSA())) {
      return SignatureAlgorithm.create_ECDSA(ToDafny.ECDSA(nativeValue.ECDSA()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return SignatureAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.SignatureAlgorithm.");
  }

  public static SymmetricSignatureAlgorithm SymmetricSignatureAlgorithm(
      software.amazon.cryptography.materialproviders.model.SymmetricSignatureAlgorithm nativeValue) {
    if (Objects.nonNull(nativeValue.HMAC())) {
      return SymmetricSignatureAlgorithm.create_HMAC(software.amazon.cryptography.primitives.ToDafny.DigestAlgorithm(nativeValue.HMAC()));
    }
    if (Objects.nonNull(nativeValue.None())) {
      return SymmetricSignatureAlgorithm.create_None(ToDafny.None(nativeValue.None()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to software.amazon.cryptography.materialproviders.internaldafny.types.SymmetricSignatureAlgorithm.");
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> AccountIdList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends EncryptedDataKey> EncryptedDataKeyList(
      List<software.amazon.cryptography.materialproviders.model.EncryptedDataKey> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.cryptography.materialproviders.ToDafny::EncryptedDataKey, 
        EncryptedDataKey._typeDescriptor());
  }

  public static DafnySequence<? extends DafnySequence<? extends Byte>> EncryptionContextKeys(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        DafnySequence._typeDescriptor(TypeDescriptor.BYTE));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> GrantTokenList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> KeyringList(
      List<IKeyring> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.cryptography.materialproviders.ToDafny::Keyring, 
        TypeDescriptor.reference(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring.class));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> KmsKeyIdList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> RegionList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Byte>> SymmetricSigningKeyList(
      List<ByteBuffer> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::ByteSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.BYTE));
  }

  public static DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> EncryptionContext(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes);
  }

  public static DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Byte>> HmacKeyMap(
      Map<String, ByteBuffer> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        software.amazon.dafny.conversion.ToDafny.Simple::ByteSequence);
  }

  public static software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier BranchKeyIdSupplier(
      IBranchKeyIdSupplier nativeValue) {
    return BranchKeyIdSupplier.wrap(nativeValue).impl();
  }

  public static software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier ClientSupplier(
      IClientSupplier nativeValue) {
    return ClientSupplier.wrap(nativeValue).impl();
  }

  public static software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache CryptographicMaterialsCache(
      ICryptographicMaterialsCache nativeValue) {
    return CryptographicMaterialsCache.wrap(nativeValue).impl();
  }

  public static software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager CryptographicMaterialsManager(
      ICryptographicMaterialsManager nativeValue) {
    return CryptographicMaterialsManager.wrap(nativeValue).impl();
  }

  public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring Keyring(
      IKeyring nativeValue) {
    return Keyring.wrap(nativeValue).impl();
  }

  public static IAwsCryptographicMaterialProvidersClient AwsCryptographicMaterialProviders(
      MaterialProviders nativeValue) {
    return nativeValue.impl();
  }
}
