// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.DIRECT__KEY__WRAPPING;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_AwsCryptographicMaterialProvidersException;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_CollectionOfErrors;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfo;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfoOnDecrypt;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidAlgorithmSuiteInfoOnEncrypt;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidDecryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidDecryptionMaterialsTransition;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidEncryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_InvalidEncryptionMaterialsTransition;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error_Opaque;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring;
import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.IllegalArgumentException;
import java.lang.String;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import software.amazon.cryptography.materialProviders.model.AesWrappingAlg;
import software.amazon.cryptography.materialProviders.model.AlgorithmSuiteId;
import software.amazon.cryptography.materialProviders.model.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialProviders.model.AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialProviders.model.CollectionOfErrors;
import software.amazon.cryptography.materialProviders.model.CommitmentPolicy;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsHierarchicalKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsRsaKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialProviders.model.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialProviders.model.CreateMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialProviders.model.DBEAlgorithmSuiteId;
import software.amazon.cryptography.materialProviders.model.DBECommitmentPolicy;
import software.amazon.cryptography.materialProviders.model.DIRECT_KEY_WRAPPING;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.DecryptionMaterials;
import software.amazon.cryptography.materialProviders.model.DerivationAlgorithm;
import software.amazon.cryptography.materialProviders.model.DiscoveryFilter;
import software.amazon.cryptography.materialProviders.model.ECDSA;
import software.amazon.cryptography.materialProviders.model.ESDKAlgorithmSuiteId;
import software.amazon.cryptography.materialProviders.model.ESDKCommitmentPolicy;
import software.amazon.cryptography.materialProviders.model.EdkWrappingAlgorithm;
import software.amazon.cryptography.materialProviders.model.Encrypt;
import software.amazon.cryptography.materialProviders.model.EncryptedDataKey;
import software.amazon.cryptography.materialProviders.model.EncryptionMaterials;
import software.amazon.cryptography.materialProviders.model.GetClientInput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.HKDF;
import software.amazon.cryptography.materialProviders.model.HierarchicalMaterials;
import software.amazon.cryptography.materialProviders.model.IDENTITY;
import software.amazon.cryptography.materialProviders.model.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.IntermediateKeyWrapping;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialProviders.model.InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialProviders.model.MaterialProvidersConfig;
import software.amazon.cryptography.materialProviders.model.NativeError;
import software.amazon.cryptography.materialProviders.model.None;
import software.amazon.cryptography.materialProviders.model.OnDecryptInput;
import software.amazon.cryptography.materialProviders.model.OnDecryptOutput;
import software.amazon.cryptography.materialProviders.model.OnEncryptInput;
import software.amazon.cryptography.materialProviders.model.OnEncryptOutput;
import software.amazon.cryptography.materialProviders.model.OpaqueError;
import software.amazon.cryptography.materialProviders.model.PaddingScheme;
import software.amazon.cryptography.materialProviders.model.SignatureAlgorithm;
import software.amazon.cryptography.materialProviders.model.SymmetricSignatureAlgorithm;
import software.amazon.cryptography.materialProviders.model.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialProviders.model.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnEncryptInput;

public class ToNative {
  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_CollectionOfErrors dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
        software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(), 
        ToNative::Error));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfoOnDecrypt Error(
      Error_InvalidAlgorithmSuiteInfoOnDecrypt dafnyValue) {
    InvalidAlgorithmSuiteInfoOnDecrypt.Builder nativeBuilder = InvalidAlgorithmSuiteInfoOnDecrypt.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidEncryptionMaterialsTransition Error(
      Error_InvalidEncryptionMaterialsTransition dafnyValue) {
    InvalidEncryptionMaterialsTransition.Builder nativeBuilder = InvalidEncryptionMaterialsTransition.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidDecryptionMaterialsTransition Error(
      Error_InvalidDecryptionMaterialsTransition dafnyValue) {
    InvalidDecryptionMaterialsTransition.Builder nativeBuilder = InvalidDecryptionMaterialsTransition.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidDecryptionMaterials Error(Error_InvalidDecryptionMaterials dafnyValue) {
    InvalidDecryptionMaterials.Builder nativeBuilder = InvalidDecryptionMaterials.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfo Error(Error_InvalidAlgorithmSuiteInfo dafnyValue) {
    InvalidAlgorithmSuiteInfo.Builder nativeBuilder = InvalidAlgorithmSuiteInfo.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static AwsCryptographicMaterialProvidersException Error(
      Error_AwsCryptographicMaterialProvidersException dafnyValue) {
    AwsCryptographicMaterialProvidersException.Builder nativeBuilder = AwsCryptographicMaterialProvidersException.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfoOnEncrypt Error(
      Error_InvalidAlgorithmSuiteInfoOnEncrypt dafnyValue) {
    InvalidAlgorithmSuiteInfoOnEncrypt.Builder nativeBuilder = InvalidAlgorithmSuiteInfoOnEncrypt.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidEncryptionMaterials Error(Error_InvalidEncryptionMaterials dafnyValue) {
    InvalidEncryptionMaterials.Builder nativeBuilder = InvalidEncryptionMaterials.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static NativeError Error(Error dafnyValue) {
    if (dafnyValue.is_InvalidAlgorithmSuiteInfoOnDecrypt()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfoOnDecrypt) dafnyValue);
    }
    if (dafnyValue.is_InvalidEncryptionMaterialsTransition()) {
      return ToNative.Error((Error_InvalidEncryptionMaterialsTransition) dafnyValue);
    }
    if (dafnyValue.is_InvalidDecryptionMaterialsTransition()) {
      return ToNative.Error((Error_InvalidDecryptionMaterialsTransition) dafnyValue);
    }
    if (dafnyValue.is_InvalidDecryptionMaterials()) {
      return ToNative.Error((Error_InvalidDecryptionMaterials) dafnyValue);
    }
    if (dafnyValue.is_InvalidAlgorithmSuiteInfo()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfo) dafnyValue);
    }
    if (dafnyValue.is_AwsCryptographicMaterialProvidersException()) {
      return ToNative.Error((Error_AwsCryptographicMaterialProvidersException) dafnyValue);
    }
    if (dafnyValue.is_InvalidAlgorithmSuiteInfoOnEncrypt()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfoOnEncrypt) dafnyValue);
    }
    if (dafnyValue.is_InvalidEncryptionMaterials()) {
      return ToNative.Error((Error_InvalidEncryptionMaterials) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static InitializeDecryptionMaterialsInput InitializeDecryptionMaterialsInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeDecryptionMaterialsInput dafnyValue) {
    InitializeDecryptionMaterialsInput.Builder nativeBuilder = InitializeDecryptionMaterialsInput.builder();
    nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    return nativeBuilder.build();
  }

  public static None None(Dafny.Aws.Cryptography.MaterialProviders.Types.None dafnyValue) {
    None.Builder nativeBuilder = None.builder();
    return nativeBuilder.build();
  }

  public static EncryptionMaterials EncryptionMaterials(
      Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptionMaterials dafnyValue) {
    EncryptionMaterials.Builder nativeBuilder = EncryptionMaterials.builder();
    nativeBuilder.algorithmSuite(ToNative.AlgorithmSuiteInfo(dafnyValue.dtor_algorithmSuite()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.encryptedDataKeys(ToNative.EncryptedDataKeyList(dafnyValue.dtor_encryptedDataKeys()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_plaintextDataKey().is_Some()) {
      nativeBuilder.plaintextDataKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_plaintextDataKey().dtor_value()));
    }
    if (dafnyValue.dtor_signingKey().is_Some()) {
      nativeBuilder.signingKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_signingKey().dtor_value()));
    }
    if (dafnyValue.dtor_symmetricSigningKeys().is_Some()) {
      nativeBuilder.symmetricSigningKeys(ToNative.SymmetricSigningKeyList(dafnyValue.dtor_symmetricSigningKeys().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateDefaultCryptographicMaterialsManagerInput CreateDefaultCryptographicMaterialsManagerInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultCryptographicMaterialsManagerInput dafnyValue) {
    CreateDefaultCryptographicMaterialsManagerInput.Builder nativeBuilder = CreateDefaultCryptographicMaterialsManagerInput.builder();
    nativeBuilder.keyring(ToNative.Keyring(dafnyValue.dtor_keyring()));
    return nativeBuilder.build();
  }

  public static OnDecryptInput OnDecryptInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptInput dafnyValue) {
    OnDecryptInput.Builder nativeBuilder = OnDecryptInput.builder();
    nativeBuilder.materials(ToNative.DecryptionMaterials(dafnyValue.dtor_materials()));
    nativeBuilder.encryptedDataKeys(ToNative.EncryptedDataKeyList(dafnyValue.dtor_encryptedDataKeys()));
    return nativeBuilder.build();
  }

  public static CreateRawAesKeyringInput CreateRawAesKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawAesKeyringInput dafnyValue) {
    CreateRawAesKeyringInput.Builder nativeBuilder = CreateRawAesKeyringInput.builder();
    nativeBuilder.keyNamespace(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyNamespace()));
    nativeBuilder.keyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyName()));
    nativeBuilder.wrappingKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_wrappingKey()));
    nativeBuilder.wrappingAlg(ToNative.AesWrappingAlg(dafnyValue.dtor_wrappingAlg()));
    return nativeBuilder.build();
  }

  public static AlgorithmSuiteInfo AlgorithmSuiteInfo(
      Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteInfo dafnyValue) {
    AlgorithmSuiteInfo.Builder nativeBuilder = AlgorithmSuiteInfo.builder();
    nativeBuilder.id(ToNative.AlgorithmSuiteId(dafnyValue.dtor_id()));
    nativeBuilder.binaryId(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_binaryId()));
    nativeBuilder.messageVersion((dafnyValue.dtor_messageVersion()));
    nativeBuilder.encrypt(ToNative.Encrypt(dafnyValue.dtor_encrypt()));
    nativeBuilder.kdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_kdf()));
    nativeBuilder.commitment(ToNative.DerivationAlgorithm(dafnyValue.dtor_commitment()));
    nativeBuilder.signature(ToNative.SignatureAlgorithm(dafnyValue.dtor_signature()));
    nativeBuilder.symmetricSignature(ToNative.SymmetricSignatureAlgorithm(dafnyValue.dtor_symmetricSignature()));
    nativeBuilder.edkWrapping(ToNative.EdkWrappingAlgorithm(dafnyValue.dtor_edkWrapping()));
    return nativeBuilder.build();
  }

  public static ValidDecryptionMaterialsTransitionInput ValidDecryptionMaterialsTransitionInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ValidDecryptionMaterialsTransitionInput dafnyValue) {
    ValidDecryptionMaterialsTransitionInput.Builder nativeBuilder = ValidDecryptionMaterialsTransitionInput.builder();
    nativeBuilder.start(ToNative.DecryptionMaterials(dafnyValue.dtor_start()));
    nativeBuilder.stop(ToNative.DecryptionMaterials(dafnyValue.dtor_stop()));
    return nativeBuilder.build();
  }

  public static CreateDefaultClientSupplierInput CreateDefaultClientSupplierInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultClientSupplierInput dafnyValue) {
    CreateDefaultClientSupplierInput.Builder nativeBuilder = CreateDefaultClientSupplierInput.builder();
    return nativeBuilder.build();
  }

  public static OnEncryptInput OnEncryptInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptInput dafnyValue) {
    OnEncryptInput.Builder nativeBuilder = OnEncryptInput.builder();
    nativeBuilder.materials(ToNative.EncryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static IntermediateKeyWrapping IntermediateKeyWrapping(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IntermediateKeyWrapping dafnyValue) {
    IntermediateKeyWrapping.Builder nativeBuilder = IntermediateKeyWrapping.builder();
    nativeBuilder.keyEncryptionKeyKdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_keyEncryptionKeyKdf()));
    nativeBuilder.macKeyKdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_macKeyKdf()));
    nativeBuilder.pdkEncryptAlgorithm(ToNative.Encrypt(dafnyValue.dtor_pdkEncryptAlgorithm()));
    return nativeBuilder.build();
  }

  public static CreateAwsKmsKeyringInput CreateAwsKmsKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsKeyringInput dafnyValue) {
    CreateAwsKmsKeyringInput.Builder nativeBuilder = CreateAwsKmsKeyringInput.builder();
    nativeBuilder.kmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetClientInput GetClientInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput dafnyValue) {
    GetClientInput.Builder nativeBuilder = GetClientInput.builder();
    nativeBuilder.region(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_region()));
    return nativeBuilder.build();
  }

  public static DiscoveryFilter DiscoveryFilter(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DiscoveryFilter dafnyValue) {
    DiscoveryFilter.Builder nativeBuilder = DiscoveryFilter.builder();
    nativeBuilder.accountIds(ToNative.AccountIdList(dafnyValue.dtor_accountIds()));
    nativeBuilder.partition(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_partition()));
    return nativeBuilder.build();
  }

  public static ECDSA ECDSA(Dafny.Aws.Cryptography.MaterialProviders.Types.ECDSA dafnyValue) {
    ECDSA.Builder nativeBuilder = ECDSA.builder();
    nativeBuilder.curve(software.amazon.cryptography.primitives.ToNative.ECDSASignatureAlgorithm(dafnyValue.dtor_curve()));
    return nativeBuilder.build();
  }

  public static DecryptMaterialsInput DecryptMaterialsInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsInput dafnyValue) {
    DecryptMaterialsInput.Builder nativeBuilder = DecryptMaterialsInput.builder();
    nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    nativeBuilder.encryptedDataKeys(ToNative.EncryptedDataKeyList(dafnyValue.dtor_encryptedDataKeys()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    if (dafnyValue.dtor_reproducedEncryptionContext().is_Some()) {
      nativeBuilder.reproducedEncryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_reproducedEncryptionContext().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkMultiKeyringInput CreateAwsKmsMrkMultiKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkMultiKeyringInput dafnyValue) {
    CreateAwsKmsMrkMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_generator().dtor_value()));
    }
    if (dafnyValue.dtor_kmsKeyIds().is_Some()) {
      nativeBuilder.kmsKeyIds(ToNative.KmsKeyIdList(dafnyValue.dtor_kmsKeyIds().dtor_value()));
    }
    if (dafnyValue.dtor_clientSupplier().is_Some()) {
      nativeBuilder.clientSupplier(ToNative.ClientSupplier(dafnyValue.dtor_clientSupplier().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING(DIRECT__KEY__WRAPPING dafnyValue) {
    DIRECT_KEY_WRAPPING.Builder nativeBuilder = DIRECT_KEY_WRAPPING.builder();
    return nativeBuilder.build();
  }

  public static HKDF HKDF(Dafny.Aws.Cryptography.MaterialProviders.Types.HKDF dafnyValue) {
    HKDF.Builder nativeBuilder = HKDF.builder();
    nativeBuilder.hmac(software.amazon.cryptography.primitives.ToNative.DigestAlgorithm(dafnyValue.dtor_hmac()));
    nativeBuilder.saltLength((dafnyValue.dtor_saltLength()));
    nativeBuilder.inputKeyLength((dafnyValue.dtor_inputKeyLength()));
    nativeBuilder.outputKeyLength((dafnyValue.dtor_outputKeyLength()));
    return nativeBuilder.build();
  }

  public static CreateRawRsaKeyringInput CreateRawRsaKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawRsaKeyringInput dafnyValue) {
    CreateRawRsaKeyringInput.Builder nativeBuilder = CreateRawRsaKeyringInput.builder();
    nativeBuilder.keyNamespace(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyNamespace()));
    nativeBuilder.keyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyName()));
    nativeBuilder.paddingScheme(ToNative.PaddingScheme(dafnyValue.dtor_paddingScheme()));
    if (dafnyValue.dtor_publicKey().is_Some()) {
      nativeBuilder.publicKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_publicKey().dtor_value()));
    }
    if (dafnyValue.dtor_privateKey().is_Some()) {
      nativeBuilder.privateKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_privateKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkDiscoveryKeyringInput CreateAwsKmsMrkDiscoveryKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryKeyringInput dafnyValue) {
    CreateAwsKmsMrkDiscoveryKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkDiscoveryKeyringInput.builder();
    nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    nativeBuilder.region(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_region()));
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMultiKeyringInput CreateAwsKmsMultiKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMultiKeyringInput dafnyValue) {
    CreateAwsKmsMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_generator().dtor_value()));
    }
    if (dafnyValue.dtor_kmsKeyIds().is_Some()) {
      nativeBuilder.kmsKeyIds(ToNative.KmsKeyIdList(dafnyValue.dtor_kmsKeyIds().dtor_value()));
    }
    if (dafnyValue.dtor_clientSupplier().is_Some()) {
      nativeBuilder.clientSupplier(ToNative.ClientSupplier(dafnyValue.dtor_clientSupplier().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static MaterialProvidersConfig MaterialProvidersConfig(
      Dafny.Aws.Cryptography.MaterialProviders.Types.MaterialProvidersConfig dafnyValue) {
    MaterialProvidersConfig.Builder nativeBuilder = MaterialProvidersConfig.builder();
    return nativeBuilder.build();
  }

  public static CreateAwsKmsDiscoveryKeyringInput CreateAwsKmsDiscoveryKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryKeyringInput dafnyValue) {
    CreateAwsKmsDiscoveryKeyringInput.Builder nativeBuilder = CreateAwsKmsDiscoveryKeyringInput.builder();
    nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsDiscoveryMultiKeyringInput CreateAwsKmsDiscoveryMultiKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryMultiKeyringInput dafnyValue) {
    CreateAwsKmsDiscoveryMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsDiscoveryMultiKeyringInput.builder();
    nativeBuilder.regions(ToNative.RegionList(dafnyValue.dtor_regions()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_clientSupplier().is_Some()) {
      nativeBuilder.clientSupplier(ToNative.ClientSupplier(dafnyValue.dtor_clientSupplier().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ValidEncryptionMaterialsTransitionInput ValidEncryptionMaterialsTransitionInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ValidEncryptionMaterialsTransitionInput dafnyValue) {
    ValidEncryptionMaterialsTransitionInput.Builder nativeBuilder = ValidEncryptionMaterialsTransitionInput.builder();
    nativeBuilder.start(ToNative.EncryptionMaterials(dafnyValue.dtor_start()));
    nativeBuilder.stop(ToNative.EncryptionMaterials(dafnyValue.dtor_stop()));
    return nativeBuilder.build();
  }

  public static OnEncryptOutput OnEncryptOutput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptOutput dafnyValue) {
    OnEncryptOutput.Builder nativeBuilder = OnEncryptOutput.builder();
    nativeBuilder.materials(ToNative.EncryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static ValidateCommitmentPolicyOnDecryptInput ValidateCommitmentPolicyOnDecryptInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnDecryptInput dafnyValue) {
    ValidateCommitmentPolicyOnDecryptInput.Builder nativeBuilder = ValidateCommitmentPolicyOnDecryptInput.builder();
    nativeBuilder.algorithm(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithm()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    return nativeBuilder.build();
  }

  public static DecryptionMaterials DecryptionMaterials(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptionMaterials dafnyValue) {
    DecryptionMaterials.Builder nativeBuilder = DecryptionMaterials.builder();
    nativeBuilder.algorithmSuite(ToNative.AlgorithmSuiteInfo(dafnyValue.dtor_algorithmSuite()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_plaintextDataKey().is_Some()) {
      nativeBuilder.plaintextDataKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_plaintextDataKey().dtor_value()));
    }
    if (dafnyValue.dtor_verificationKey().is_Some()) {
      nativeBuilder.verificationKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_verificationKey().dtor_value()));
    }
    if (dafnyValue.dtor_symmetricSigningKey().is_Some()) {
      nativeBuilder.symmetricSigningKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_symmetricSigningKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ByteBuffer GetAlgorithmSuiteInfoInput(DafnySequence<? extends Byte> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue);
  }

  public static CreateAwsKmsMrkDiscoveryMultiKeyringInput CreateAwsKmsMrkDiscoveryMultiKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyValue) {
    CreateAwsKmsMrkDiscoveryMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkDiscoveryMultiKeyringInput.builder();
    nativeBuilder.regions(ToNative.RegionList(dafnyValue.dtor_regions()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_clientSupplier().is_Some()) {
      nativeBuilder.clientSupplier(ToNative.ClientSupplier(dafnyValue.dtor_clientSupplier().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateMultiKeyringInput CreateMultiKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateMultiKeyringInput dafnyValue) {
    CreateMultiKeyringInput.Builder nativeBuilder = CreateMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(ToNative.Keyring(dafnyValue.dtor_generator().dtor_value()));
    }
    nativeBuilder.childKeyrings(ToNative.KeyringList(dafnyValue.dtor_childKeyrings()));
    return nativeBuilder.build();
  }

  public static GetEncryptionMaterialsOutput GetEncryptionMaterialsOutput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput dafnyValue) {
    GetEncryptionMaterialsOutput.Builder nativeBuilder = GetEncryptionMaterialsOutput.builder();
    nativeBuilder.encryptionMaterials(ToNative.EncryptionMaterials(dafnyValue.dtor_encryptionMaterials()));
    return nativeBuilder.build();
  }

  public static ValidateCommitmentPolicyOnEncryptInput ValidateCommitmentPolicyOnEncryptInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnEncryptInput dafnyValue) {
    ValidateCommitmentPolicyOnEncryptInput.Builder nativeBuilder = ValidateCommitmentPolicyOnEncryptInput.builder();
    nativeBuilder.algorithm(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithm()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    return nativeBuilder.build();
  }

  public static IDENTITY IDENTITY(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IDENTITY dafnyValue) {
    IDENTITY.Builder nativeBuilder = IDENTITY.builder();
    return nativeBuilder.build();
  }

  public static InitializeEncryptionMaterialsInput InitializeEncryptionMaterialsInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeEncryptionMaterialsInput dafnyValue) {
    InitializeEncryptionMaterialsInput.Builder nativeBuilder = InitializeEncryptionMaterialsInput.builder();
    nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_signingKey().is_Some()) {
      nativeBuilder.signingKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_signingKey().dtor_value()));
    }
    if (dafnyValue.dtor_verificationKey().is_Some()) {
      nativeBuilder.verificationKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_verificationKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DecryptMaterialsOutput DecryptMaterialsOutput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput dafnyValue) {
    DecryptMaterialsOutput.Builder nativeBuilder = DecryptMaterialsOutput.builder();
    nativeBuilder.decryptionMaterials(ToNative.DecryptionMaterials(dafnyValue.dtor_decryptionMaterials()));
    return nativeBuilder.build();
  }

  public static HierarchicalMaterials HierarchicalMaterials(
      Dafny.Aws.Cryptography.MaterialProviders.Types.HierarchicalMaterials dafnyValue) {
    HierarchicalMaterials.Builder nativeBuilder = HierarchicalMaterials.builder();
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static GetEncryptionMaterialsInput GetEncryptionMaterialsInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsInput dafnyValue) {
    GetEncryptionMaterialsInput.Builder nativeBuilder = GetEncryptionMaterialsInput.builder();
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    if (dafnyValue.dtor_algorithmSuiteId().is_Some()) {
      nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId().dtor_value()));
    }
    if (dafnyValue.dtor_maxPlaintextLength().is_Some()) {
      nativeBuilder.maxPlaintextLength((dafnyValue.dtor_maxPlaintextLength().dtor_value()));
    }
    if (dafnyValue.dtor_requiredEncryptionContextKeys().is_Some()) {
      nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsRsaKeyringInput CreateAwsKmsRsaKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsRsaKeyringInput dafnyValue) {
    CreateAwsKmsRsaKeyringInput.Builder nativeBuilder = CreateAwsKmsRsaKeyringInput.builder();
    if (dafnyValue.dtor_publicKey().is_Some()) {
      nativeBuilder.publicKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_publicKey().dtor_value()));
    }
    nativeBuilder.kmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.encryptionAlgorithm(Dafny.Com.Amazonaws.Kms.ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_encryptionAlgorithm()));
    if (dafnyValue.dtor_kmsClient().is_Some()) {
      nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsHierarchicalKeyringInput CreateAwsKmsHierarchicalKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsHierarchicalKeyringInput dafnyValue) {
    CreateAwsKmsHierarchicalKeyringInput.Builder nativeBuilder = CreateAwsKmsHierarchicalKeyringInput.builder();
    nativeBuilder.branchKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyId()));
    nativeBuilder.kmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient()));
    nativeBuilder.ddbClient(Dafny.Com.Amazonaws.Dynamodb.ToNative.DynamoDB_20120810(dafnyValue.dtor_ddbClient()));
    nativeBuilder.branchKeyStoreArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyStoreArn()));
    nativeBuilder.ttlSeconds((dafnyValue.dtor_ttlSeconds()));
    if (dafnyValue.dtor_maxCacheSize().is_Some()) {
      nativeBuilder.maxCacheSize((dafnyValue.dtor_maxCacheSize().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkKeyringInput CreateAwsKmsMrkKeyringInput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkKeyringInput dafnyValue) {
    CreateAwsKmsMrkKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkKeyringInput.builder();
    nativeBuilder.kmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.KeyManagementService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static EncryptedDataKey EncryptedDataKey(
      Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptedDataKey dafnyValue) {
    EncryptedDataKey.Builder nativeBuilder = EncryptedDataKey.builder();
    nativeBuilder.keyProviderId(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_keyProviderId()));
    nativeBuilder.keyProviderInfo(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_keyProviderInfo()));
    nativeBuilder.ciphertext(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_ciphertext()));
    return nativeBuilder.build();
  }

  public static OnDecryptOutput OnDecryptOutput(
      Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptOutput dafnyValue) {
    OnDecryptOutput.Builder nativeBuilder = OnDecryptOutput.builder();
    nativeBuilder.materials(ToNative.DecryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static DBEAlgorithmSuiteId DBEAlgorithmSuiteId(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DBEAlgorithmSuiteId dafnyValue) {
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384()) {
      return DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384()) {
      return DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.DBEAlgorithmSuiteId matches the input : " + dafnyValue);
  }

  public static DBECommitmentPolicy DBECommitmentPolicy(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DBECommitmentPolicy dafnyValue) {
    if (dafnyValue.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT()) {
      return DBECommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.DBECommitmentPolicy matches the input : " + dafnyValue);
  }

  public static ESDKAlgorithmSuiteId ESDKAlgorithmSuiteId(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKAlgorithmSuiteId dafnyValue) {
    if (dafnyValue.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF()) {
      return ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
    }
    if (dafnyValue.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF()) {
      return ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF()) {
      return ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
    }
    if (dafnyValue.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256()) {
      return ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
    }
    if (dafnyValue.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256()) {
      return ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256()) {
      return ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
    }
    if (dafnyValue.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256()) {
      return ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
    }
    if (dafnyValue.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384()) {
      return ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384()) {
      return ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY()) {
      return ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384()) {
      return ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.ESDKAlgorithmSuiteId matches the input : " + dafnyValue);
  }

  public static AesWrappingAlg AesWrappingAlg(
      Dafny.Aws.Cryptography.MaterialProviders.Types.AesWrappingAlg dafnyValue) {
    if (dafnyValue.is_ALG__AES128__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
    }
    if (dafnyValue.is_ALG__AES192__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
    }
    if (dafnyValue.is_ALG__AES256__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.AesWrappingAlg matches the input : " + dafnyValue);
  }

  public static PaddingScheme PaddingScheme(
      Dafny.Aws.Cryptography.MaterialProviders.Types.PaddingScheme dafnyValue) {
    if (dafnyValue.is_PKCS1()) {
      return PaddingScheme.PKCS1;
    }
    if (dafnyValue.is_OAEP__SHA1__MGF1()) {
      return PaddingScheme.OAEP_SHA1_MGF1;
    }
    if (dafnyValue.is_OAEP__SHA256__MGF1()) {
      return PaddingScheme.OAEP_SHA256_MGF1;
    }
    if (dafnyValue.is_OAEP__SHA384__MGF1()) {
      return PaddingScheme.OAEP_SHA384_MGF1;
    }
    if (dafnyValue.is_OAEP__SHA512__MGF1()) {
      return PaddingScheme.OAEP_SHA512_MGF1;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.PaddingScheme matches the input : " + dafnyValue);
  }

  public static ESDKCommitmentPolicy ESDKCommitmentPolicy(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ESDKCommitmentPolicy dafnyValue) {
    if (dafnyValue.is_FORBID__ENCRYPT__ALLOW__DECRYPT()) {
      return ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
    }
    if (dafnyValue.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT()) {
      return ESDKCommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
    }
    if (dafnyValue.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT()) {
      return ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialProviders.model.ESDKCommitmentPolicy matches the input : " + dafnyValue);
  }

  public static AlgorithmSuiteId AlgorithmSuiteId(
      Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteId dafnyValue) {
    AlgorithmSuiteId.Builder nativeBuilder = AlgorithmSuiteId.builder();
    if (dafnyValue.is_ESDK()) {
      nativeBuilder.ESDK(ToNative.ESDKAlgorithmSuiteId(dafnyValue.dtor_ESDK()));
    }
    if (dafnyValue.is_DBE()) {
      nativeBuilder.DBE(ToNative.DBEAlgorithmSuiteId(dafnyValue.dtor_DBE()));
    }
    return nativeBuilder.build();
  }

  public static DerivationAlgorithm DerivationAlgorithm(
      Dafny.Aws.Cryptography.MaterialProviders.Types.DerivationAlgorithm dafnyValue) {
    DerivationAlgorithm.Builder nativeBuilder = DerivationAlgorithm.builder();
    if (dafnyValue.is_HKDF()) {
      nativeBuilder.HKDF(ToNative.HKDF(dafnyValue.dtor_HKDF()));
    }
    if (dafnyValue.is_IDENTITY()) {
      nativeBuilder.IDENTITY(ToNative.IDENTITY(dafnyValue.dtor_IDENTITY()));
    }
    if (dafnyValue.is_None()) {
      nativeBuilder.None(ToNative.None(dafnyValue.dtor_None()));
    }
    return nativeBuilder.build();
  }

  public static SignatureAlgorithm SignatureAlgorithm(
      Dafny.Aws.Cryptography.MaterialProviders.Types.SignatureAlgorithm dafnyValue) {
    SignatureAlgorithm.Builder nativeBuilder = SignatureAlgorithm.builder();
    if (dafnyValue.is_ECDSA()) {
      nativeBuilder.ECDSA(ToNative.ECDSA(dafnyValue.dtor_ECDSA()));
    }
    if (dafnyValue.is_None()) {
      nativeBuilder.None(ToNative.None(dafnyValue.dtor_None()));
    }
    return nativeBuilder.build();
  }

  public static CommitmentPolicy CommitmentPolicy(
      Dafny.Aws.Cryptography.MaterialProviders.Types.CommitmentPolicy dafnyValue) {
    CommitmentPolicy.Builder nativeBuilder = CommitmentPolicy.builder();
    if (dafnyValue.is_ESDK()) {
      nativeBuilder.ESDK(ToNative.ESDKCommitmentPolicy(dafnyValue.dtor_ESDK()));
    }
    if (dafnyValue.is_DBE()) {
      nativeBuilder.DBE(ToNative.DBECommitmentPolicy(dafnyValue.dtor_DBE()));
    }
    return nativeBuilder.build();
  }

  public static EdkWrappingAlgorithm EdkWrappingAlgorithm(
      Dafny.Aws.Cryptography.MaterialProviders.Types.EdkWrappingAlgorithm dafnyValue) {
    EdkWrappingAlgorithm.Builder nativeBuilder = EdkWrappingAlgorithm.builder();
    if (dafnyValue.is_DIRECT__KEY__WRAPPING()) {
      nativeBuilder.DIRECT_KEY_WRAPPING(ToNative.DIRECT_KEY_WRAPPING(dafnyValue.dtor_DIRECT__KEY__WRAPPING()));
    }
    if (dafnyValue.is_IntermediateKeyWrapping()) {
      nativeBuilder.IntermediateKeyWrapping(ToNative.IntermediateKeyWrapping(dafnyValue.dtor_IntermediateKeyWrapping()));
    }
    return nativeBuilder.build();
  }

  public static Encrypt Encrypt(Dafny.Aws.Cryptography.MaterialProviders.Types.Encrypt dafnyValue) {
    Encrypt.Builder nativeBuilder = Encrypt.builder();
    if (dafnyValue.is_AES__GCM()) {
      nativeBuilder.AES_GCM(software.amazon.cryptography.primitives.ToNative.AES_GCM(dafnyValue.dtor_AES__GCM()));
    }
    return nativeBuilder.build();
  }

  public static SymmetricSignatureAlgorithm SymmetricSignatureAlgorithm(
      Dafny.Aws.Cryptography.MaterialProviders.Types.SymmetricSignatureAlgorithm dafnyValue) {
    SymmetricSignatureAlgorithm.Builder nativeBuilder = SymmetricSignatureAlgorithm.builder();
    if (dafnyValue.is_HMAC()) {
      nativeBuilder.HMAC(software.amazon.cryptography.primitives.ToNative.DigestAlgorithm(dafnyValue.dtor_HMAC()));
    }
    if (dafnyValue.is_None()) {
      nativeBuilder.None(ToNative.None(dafnyValue.dtor_None()));
    }
    return nativeBuilder.build();
  }

  public static List<Keyring> KeyringList(DafnySequence<? extends IKeyring> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.materialProviders.ToNative::Keyring);
  }

  public static List<ByteBuffer> SymmetricSigningKeyList(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::ByteBuffer);
  }

  public static List<String> EncryptionContextKeys(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes);
  }

  public static List<String> AccountIdList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> RegionList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> GrantTokenList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> KmsKeyIdList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<EncryptedDataKey> EncryptedDataKeyList(
      DafnySequence<? extends Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptedDataKey> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.materialProviders.ToNative::EncryptedDataKey);
  }

  public static Map<String, String> EncryptionContext(
      DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes, 
        software.amazon.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes);
  }

  public static CryptographicMaterialsManager CryptographicMaterialsManager(
      ICryptographicMaterialsManager dafnyValue) {
    return CryptographicMaterialsManager.wrap(dafnyValue);
  }

  public static Keyring Keyring(IKeyring dafnyValue) {
    return Keyring.wrap(dafnyValue);
  }

  public static ClientSupplier ClientSupplier(IClientSupplier dafnyValue) {
    return ClientSupplier.wrap(dafnyValue);
  }
}
