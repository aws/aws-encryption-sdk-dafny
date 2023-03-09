// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.AesWrappingAlg;
import Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteId;
import Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteInfo;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CommitmentPolicy;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsHierarchicalKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsRsaKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultClientSupplierInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultCryptographicMaterialsManagerInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawAesKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawRsaKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DBEAlgorithmSuiteId;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DBECommitmentPolicy;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DIRECT__KEY__WRAPPING;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DerivationAlgorithm;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DiscoveryFilter;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ECDSA;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKAlgorithmSuiteId;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKCommitmentPolicy;
import Dafny.Aws.Cryptography.MaterialProviders.Types.EdkWrappingAlgorithm;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Encrypt;
import Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptedDataKey;
import Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_AwsCryptographicMaterialProvidersException;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfo;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfoOnDecrypt;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfoOnEncrypt;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidDecryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidDecryptionMaterialsTransition;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidEncryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidEncryptionMaterialsTransition;
import Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.HKDF;
import Dafny.Aws.Cryptography.MaterialProviders.Types.HierarchicalMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IDENTITY;
import Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeDecryptionMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeEncryptionMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IntermediateKeyWrapping;
import Dafny.Aws.Cryptography.MaterialProviders.Types.MaterialProvidersConfig;
import Dafny.Aws.Cryptography.MaterialProviders.Types.None;
import Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptOutput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptOutput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.PaddingScheme;
import Dafny.Aws.Cryptography.MaterialProviders.Types.SignatureAlgorithm;
import Dafny.Aws.Cryptography.MaterialProviders.Types.SymmetricSignatureAlgorithm;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidDecryptionMaterialsTransitionInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidEncryptionMaterialsTransitionInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnDecryptInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnEncryptInput;
import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.ECDSASignatureAlgorithm;
import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDB__20120810Client;
import Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
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
import software.amazon.cryptography.materialProviders.model.DIRECT_KEY_WRAPPING;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.NativeError;
import software.amazon.cryptography.materialProviders.model.OpaqueError;

public class ToDafny {
  public static Error Error(NativeError nativeValue) {
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnDecrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnDecrypt) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterialsTransition) {
      return ToDafny.Error((InvalidEncryptionMaterialsTransition) nativeValue);
    }
    if (nativeValue instanceof InvalidDecryptionMaterialsTransition) {
      return ToDafny.Error((InvalidDecryptionMaterialsTransition) nativeValue);
    }
    if (nativeValue instanceof InvalidDecryptionMaterials) {
      return ToDafny.Error((InvalidDecryptionMaterials) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfo) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfo) nativeValue);
    }
    if (nativeValue instanceof AwsCryptographicMaterialProvidersException) {
      return ToDafny.Error((AwsCryptographicMaterialProvidersException) nativeValue);
    }
    if (nativeValue instanceof InvalidAlgorithmSuiteInfoOnEncrypt) {
      return ToDafny.Error((InvalidAlgorithmSuiteInfoOnEncrypt) nativeValue);
    }
    if (nativeValue instanceof InvalidEncryptionMaterials) {
      return ToDafny.Error((InvalidEncryptionMaterials) nativeValue);
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

  public static InitializeDecryptionMaterialsInput InitializeDecryptionMaterialsInput(
      software.amazon.cryptography.materialProviders.model.InitializeDecryptionMaterialsInput nativeValue) {
    AlgorithmSuiteId algorithmSuiteId;
    algorithmSuiteId = ToDafny.AlgorithmSuiteId(nativeValue.algorithmSuiteId());
    DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> encryptionContext;
    encryptionContext = ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends DafnySequence<? extends Byte>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys());
    return new InitializeDecryptionMaterialsInput(algorithmSuiteId, encryptionContext, requiredEncryptionContextKeys);
  }

  public static None None(software.amazon.cryptography.materialProviders.model.None nativeValue) {
    return new None();
  }

  public static EncryptionMaterials EncryptionMaterials(
      software.amazon.cryptography.materialProviders.model.EncryptionMaterials nativeValue) {
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
    symmetricSigningKeys = Objects.nonNull(nativeValue.symmetricSigningKeys()) ?
        Option.create_Some(ToDafny.SymmetricSigningKeyList(nativeValue.symmetricSigningKeys()))
        : Option.create_None();
    return new EncryptionMaterials(algorithmSuite, encryptionContext, encryptedDataKeys, requiredEncryptionContextKeys, plaintextDataKey, signingKey, symmetricSigningKeys);
  }

  public static CreateDefaultCryptographicMaterialsManagerInput CreateDefaultCryptographicMaterialsManagerInput(
      software.amazon.cryptography.materialProviders.model.CreateDefaultCryptographicMaterialsManagerInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring keyring;
    keyring = ToDafny.Keyring(nativeValue.keyring());
    return new CreateDefaultCryptographicMaterialsManagerInput(keyring);
  }

  public static OnDecryptInput OnDecryptInput(
      software.amazon.cryptography.materialProviders.model.OnDecryptInput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    DafnySequence<? extends EncryptedDataKey> encryptedDataKeys;
    encryptedDataKeys = ToDafny.EncryptedDataKeyList(nativeValue.encryptedDataKeys());
    return new OnDecryptInput(materials, encryptedDataKeys);
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

  public static ValidDecryptionMaterialsTransitionInput ValidDecryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialProviders.model.ValidDecryptionMaterialsTransitionInput nativeValue) {
    DecryptionMaterials start;
    start = ToDafny.DecryptionMaterials(nativeValue.start());
    DecryptionMaterials stop;
    stop = ToDafny.DecryptionMaterials(nativeValue.stop());
    return new ValidDecryptionMaterialsTransitionInput(start, stop);
  }

  public static CreateDefaultClientSupplierInput CreateDefaultClientSupplierInput(
      software.amazon.cryptography.materialProviders.model.CreateDefaultClientSupplierInput nativeValue) {
    return new CreateDefaultClientSupplierInput();
  }

  public static OnEncryptInput OnEncryptInput(
      software.amazon.cryptography.materialProviders.model.OnEncryptInput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptInput(materials);
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

  public static CreateAwsKmsKeyringInput CreateAwsKmsKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient());
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsKeyringInput(kmsKeyId, kmsClient, grantTokens);
  }

  public static GetClientInput GetClientInput(
      software.amazon.cryptography.materialProviders.model.GetClientInput nativeValue) {
    DafnySequence<? extends Character> region;
    region = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.region());
    return new GetClientInput(region);
  }

  public static DiscoveryFilter DiscoveryFilter(
      software.amazon.cryptography.materialProviders.model.DiscoveryFilter nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> accountIds;
    accountIds = ToDafny.AccountIdList(nativeValue.accountIds());
    DafnySequence<? extends Character> partition;
    partition = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.partition());
    return new DiscoveryFilter(accountIds, partition);
  }

  public static ECDSA ECDSA(
      software.amazon.cryptography.materialProviders.model.ECDSA nativeValue) {
    ECDSASignatureAlgorithm curve;
    curve = software.amazon.cryptography.primitives.ToDafny.ECDSASignatureAlgorithm(nativeValue.curve());
    return new ECDSA(curve);
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
    Option<DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>>> reproducedEncryptionContext;
    reproducedEncryptionContext = Objects.nonNull(nativeValue.reproducedEncryptionContext()) ?
        Option.create_Some(ToDafny.EncryptionContext(nativeValue.reproducedEncryptionContext()))
        : Option.create_None();
    return new DecryptMaterialsInput(algorithmSuiteId, commitmentPolicy, encryptedDataKeys, encryptionContext, reproducedEncryptionContext);
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
    Option<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static DIRECT__KEY__WRAPPING DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING nativeValue) {
    return new DIRECT__KEY__WRAPPING();
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

  public static CreateAwsKmsMrkDiscoveryKeyringInput CreateAwsKmsMrkDiscoveryKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryKeyringInput nativeValue) {
    IKeyManagementServiceClient kmsClient;
    kmsClient = Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient());
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
    Option<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMultiKeyringInput(generator, kmsKeyIds, clientSupplier, grantTokens);
  }

  public static MaterialProvidersConfig MaterialProvidersConfig(
      software.amazon.cryptography.materialProviders.model.MaterialProvidersConfig nativeValue) {
    return new MaterialProvidersConfig();
  }

  public static CreateAwsKmsDiscoveryKeyringInput CreateAwsKmsDiscoveryKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryKeyringInput nativeValue) {
    IKeyManagementServiceClient kmsClient;
    kmsClient = Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient());
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

  public static CreateAwsKmsDiscoveryMultiKeyringInput CreateAwsKmsDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static ValidEncryptionMaterialsTransitionInput ValidEncryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialProviders.model.ValidEncryptionMaterialsTransitionInput nativeValue) {
    EncryptionMaterials start;
    start = ToDafny.EncryptionMaterials(nativeValue.start());
    EncryptionMaterials stop;
    stop = ToDafny.EncryptionMaterials(nativeValue.stop());
    return new ValidEncryptionMaterialsTransitionInput(start, stop);
  }

  public static OnEncryptOutput OnEncryptOutput(
      software.amazon.cryptography.materialProviders.model.OnEncryptOutput nativeValue) {
    EncryptionMaterials materials;
    materials = ToDafny.EncryptionMaterials(nativeValue.materials());
    return new OnEncryptOutput(materials);
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

  public static DafnySequence<? extends Byte> GetAlgorithmSuiteInfoInput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> binaryId;
    binaryId = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return binaryId;
  }

  public static CreateAwsKmsMrkDiscoveryMultiKeyringInput CreateAwsKmsMrkDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeValue) {
    DafnySequence<? extends DafnySequence<? extends Character>> regions;
    regions = ToDafny.RegionList(nativeValue.regions());
    Option<DiscoveryFilter> discoveryFilter;
    discoveryFilter = Objects.nonNull(nativeValue.discoveryFilter()) ?
        Option.create_Some(ToDafny.DiscoveryFilter(nativeValue.discoveryFilter()))
        : Option.create_None();
    Option<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier> clientSupplier;
    clientSupplier = Objects.nonNull(nativeValue.clientSupplier()) ?
        Option.create_Some(ToDafny.ClientSupplier(nativeValue.clientSupplier()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkDiscoveryMultiKeyringInput(regions, discoveryFilter, clientSupplier, grantTokens);
  }

  public static CreateMultiKeyringInput CreateMultiKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateMultiKeyringInput nativeValue) {
    Option<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring> generator;
    generator = Objects.nonNull(nativeValue.generator()) ?
        Option.create_Some(ToDafny.Keyring(nativeValue.generator()))
        : Option.create_None();
    DafnySequence<? extends Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring> childKeyrings;
    childKeyrings = ToDafny.KeyringList(nativeValue.childKeyrings());
    return new CreateMultiKeyringInput(generator, childKeyrings);
  }

  public static GetEncryptionMaterialsOutput GetEncryptionMaterialsOutput(
      software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput nativeValue) {
    EncryptionMaterials encryptionMaterials;
    encryptionMaterials = ToDafny.EncryptionMaterials(nativeValue.encryptionMaterials());
    return new GetEncryptionMaterialsOutput(encryptionMaterials);
  }

  public static ValidateCommitmentPolicyOnEncryptInput ValidateCommitmentPolicyOnEncryptInput(
      software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnEncryptInput nativeValue) {
    AlgorithmSuiteId algorithm;
    algorithm = ToDafny.AlgorithmSuiteId(nativeValue.algorithm());
    CommitmentPolicy commitmentPolicy;
    commitmentPolicy = ToDafny.CommitmentPolicy(nativeValue.commitmentPolicy());
    return new ValidateCommitmentPolicyOnEncryptInput(algorithm, commitmentPolicy);
  }

  public static IDENTITY IDENTITY(
      software.amazon.cryptography.materialProviders.model.IDENTITY nativeValue) {
    return new IDENTITY();
  }

  public static InitializeEncryptionMaterialsInput InitializeEncryptionMaterialsInput(
      software.amazon.cryptography.materialProviders.model.InitializeEncryptionMaterialsInput nativeValue) {
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

  public static DecryptMaterialsOutput DecryptMaterialsOutput(
      software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput nativeValue) {
    DecryptionMaterials decryptionMaterials;
    decryptionMaterials = ToDafny.DecryptionMaterials(nativeValue.decryptionMaterials());
    return new DecryptMaterialsOutput(decryptionMaterials);
  }

  public static HierarchicalMaterials HierarchicalMaterials(
      software.amazon.cryptography.materialProviders.model.HierarchicalMaterials nativeValue) {
    DafnySequence<? extends Byte> branchKeyVersion;
    branchKeyVersion = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.branchKeyVersion());
    DafnySequence<? extends Byte> branchKey;
    branchKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.branchKey());
    return new HierarchicalMaterials(branchKeyVersion, branchKey);
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
    Option<DafnySequence<? extends DafnySequence<? extends Byte>>> requiredEncryptionContextKeys;
    requiredEncryptionContextKeys = Objects.nonNull(nativeValue.requiredEncryptionContextKeys()) ?
        Option.create_Some(ToDafny.EncryptionContextKeys(nativeValue.requiredEncryptionContextKeys()))
        : Option.create_None();
    return new GetEncryptionMaterialsInput(encryptionContext, commitmentPolicy, algorithmSuiteId, maxPlaintextLength, requiredEncryptionContextKeys);
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
        Option.create_Some(Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsRsaKeyringInput(publicKey, kmsKeyId, encryptionAlgorithm, kmsClient, grantTokens);
  }

  public static CreateAwsKmsHierarchicalKeyringInput CreateAwsKmsHierarchicalKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsHierarchicalKeyringInput nativeValue) {
    DafnySequence<? extends Character> branchKeyId;
    branchKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyId());
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient());
    IDynamoDB__20120810Client ddbClient;
    ddbClient = Dafny.Com.Amazonaws.Dynamodb.ToDafny.DynamoDB_20120810(nativeValue.ddbClient());
    DafnySequence<? extends Character> branchKeyStoreArn;
    branchKeyStoreArn = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyStoreArn());
    Long ttlSeconds;
    ttlSeconds = (nativeValue.ttlSeconds());
    Option<Integer> maxCacheSize;
    maxCacheSize = Objects.nonNull(nativeValue.maxCacheSize()) ?
        Option.create_Some((nativeValue.maxCacheSize()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsHierarchicalKeyringInput(branchKeyId, kmsKeyId, kmsClient, ddbClient, branchKeyStoreArn, ttlSeconds, maxCacheSize, grantTokens);
  }

  public static CreateAwsKmsMrkKeyringInput CreateAwsKmsMrkKeyringInput(
      software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkKeyringInput nativeValue) {
    DafnySequence<? extends Character> kmsKeyId;
    kmsKeyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.kmsKeyId());
    IKeyManagementServiceClient kmsClient;
    kmsClient = Dafny.Com.Amazonaws.Kms.ToDafny.KeyManagementService(nativeValue.kmsClient());
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = Objects.nonNull(nativeValue.grantTokens()) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateAwsKmsMrkKeyringInput(kmsKeyId, kmsClient, grantTokens);
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

  public static OnDecryptOutput OnDecryptOutput(
      software.amazon.cryptography.materialProviders.model.OnDecryptOutput nativeValue) {
    DecryptionMaterials materials;
    materials = ToDafny.DecryptionMaterials(nativeValue.materials());
    return new OnDecryptOutput(materials);
  }

  public static Error Error(InvalidAlgorithmSuiteInfoOnDecrypt nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidAlgorithmSuiteInfoOnDecrypt(message);
  }

  public static Error Error(InvalidEncryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidEncryptionMaterialsTransition(message);
  }

  public static Error Error(InvalidDecryptionMaterialsTransition nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_InvalidDecryptionMaterialsTransition(message);
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

  public static Error Error(AwsCryptographicMaterialProvidersException nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_AwsCryptographicMaterialProvidersException(message);
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

  public static DBECommitmentPolicy DBECommitmentPolicy(
      software.amazon.cryptography.materialProviders.model.DBECommitmentPolicy nativeValue) {
    switch (nativeValue) {
      case REQUIRE_ENCRYPT_REQUIRE_DECRYPT: {
        return DBECommitmentPolicy.create();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.DBECommitmentPolicy.");
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

  public static Encrypt Encrypt(
      software.amazon.cryptography.materialProviders.model.Encrypt nativeValue) {
    if (Objects.nonNull(nativeValue.AES_GCM())) {
      return Encrypt.create(software.amazon.cryptography.primitives.ToDafny.AES_GCM(nativeValue.AES_GCM()));
    }
    throw new IllegalArgumentException("Cannot convert " + nativeValue + " to Dafny.Aws.Cryptography.MaterialProviders.Types.Encrypt.");
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

  public static DafnySequence<? extends Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring> KeyringList(
      List<Keyring> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.cryptography.materialProviders.ToDafny::Keyring, 
        TypeDescriptor.reference(Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring.class));
  }

  public static DafnySequence<? extends DafnySequence<? extends Byte>> SymmetricSigningKeyList(
      List<ByteBuffer> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::ByteSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.BYTE));
  }

  public static DafnySequence<? extends DafnySequence<? extends Byte>> EncryptionContextKeys(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        DafnySequence._typeDescriptor(TypeDescriptor.BYTE));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> AccountIdList(
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

  public static DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> EncryptionContext(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes);
  }

  public static Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager CryptographicMaterialsManager(
      ICryptographicMaterialsManager nativeValue) {
    return CryptographicMaterialsManager.wrap(nativeValue).impl();
  }

  public static Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring Keyring(
      IKeyring nativeValue) {
    return Keyring.wrap(nativeValue).impl();
  }

  public static Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier ClientSupplier(
      IClientSupplier nativeValue) {
    return ClientSupplier.wrap(nativeValue).impl();
  }
}
