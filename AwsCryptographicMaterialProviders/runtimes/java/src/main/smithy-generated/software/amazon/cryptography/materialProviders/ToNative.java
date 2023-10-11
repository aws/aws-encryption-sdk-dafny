// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.lang.String;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import software.amazon.cryptography.materialproviders.internaldafny.types.DIRECT__KEY__WRAPPING;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_CollectionOfErrors;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_EntryAlreadyExists;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_EntryDoesNotExist;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidDecryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidEncryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error_Opaque;
import software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient;
import software.amazon.cryptography.materialproviders.model.AesWrappingAlg;
import software.amazon.cryptography.materialproviders.model.AlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.model.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.model.AwsCryptographicMaterialProvidersException;
import software.amazon.cryptography.materialproviders.model.BeaconKeyMaterials;
import software.amazon.cryptography.materialproviders.model.BranchKeyMaterials;
import software.amazon.cryptography.materialproviders.model.CollectionOfErrors;
import software.amazon.cryptography.materialproviders.model.CommitmentPolicy;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsHierarchicalKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsRsaKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateCryptographicMaterialsCacheInput;
import software.amazon.cryptography.materialproviders.model.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialproviders.model.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialproviders.model.CreateExpectedEncryptionContextCMMInput;
import software.amazon.cryptography.materialproviders.model.CreateMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialproviders.model.DBEAlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.model.DBECommitmentPolicy;
import software.amazon.cryptography.materialproviders.model.DIRECT_KEY_WRAPPING;
import software.amazon.cryptography.materialproviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialproviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialproviders.model.DecryptionMaterials;
import software.amazon.cryptography.materialproviders.model.DeleteCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.DerivationAlgorithm;
import software.amazon.cryptography.materialproviders.model.DiscoveryFilter;
import software.amazon.cryptography.materialproviders.model.ECDSA;
import software.amazon.cryptography.materialproviders.model.ESDKAlgorithmSuiteId;
import software.amazon.cryptography.materialproviders.model.ESDKCommitmentPolicy;
import software.amazon.cryptography.materialproviders.model.EdkWrappingAlgorithm;
import software.amazon.cryptography.materialproviders.model.Encrypt;
import software.amazon.cryptography.materialproviders.model.EncryptedDataKey;
import software.amazon.cryptography.materialproviders.model.EncryptionMaterials;
import software.amazon.cryptography.materialproviders.model.EntryAlreadyExists;
import software.amazon.cryptography.materialproviders.model.EntryDoesNotExist;
import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdInput;
import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdOutput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialproviders.model.GetClientInput;
import software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsOutput;
import software.amazon.cryptography.materialproviders.model.HKDF;
import software.amazon.cryptography.materialproviders.model.IDENTITY;
import software.amazon.cryptography.materialproviders.model.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.IntermediateKeyWrapping;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfoOnDecrypt;
import software.amazon.cryptography.materialproviders.model.InvalidAlgorithmSuiteInfoOnEncrypt;
import software.amazon.cryptography.materialproviders.model.InvalidDecryptionMaterials;
import software.amazon.cryptography.materialproviders.model.InvalidDecryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.model.InvalidEncryptionMaterials;
import software.amazon.cryptography.materialproviders.model.InvalidEncryptionMaterialsTransition;
import software.amazon.cryptography.materialproviders.model.MaterialProvidersConfig;
import software.amazon.cryptography.materialproviders.model.Materials;
import software.amazon.cryptography.materialproviders.model.None;
import software.amazon.cryptography.materialproviders.model.OnDecryptInput;
import software.amazon.cryptography.materialproviders.model.OnDecryptOutput;
import software.amazon.cryptography.materialproviders.model.OnEncryptInput;
import software.amazon.cryptography.materialproviders.model.OnEncryptOutput;
import software.amazon.cryptography.materialproviders.model.OpaqueError;
import software.amazon.cryptography.materialproviders.model.PaddingScheme;
import software.amazon.cryptography.materialproviders.model.PutCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.SignatureAlgorithm;
import software.amazon.cryptography.materialproviders.model.SymmetricSignatureAlgorithm;
import software.amazon.cryptography.materialproviders.model.UpdaterUsageMetadataInput;
import software.amazon.cryptography.materialproviders.model.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.model.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnEncryptInput;

public class ToNative {
  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_CollectionOfErrors dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
        software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(), 
        ToNative::Error));
    return nativeBuilder.build();
  }

  public static AwsCryptographicMaterialProvidersException Error(
      Error_AwsCryptographicMaterialProvidersException dafnyValue) {
    AwsCryptographicMaterialProvidersException.Builder nativeBuilder = AwsCryptographicMaterialProvidersException.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static EntryAlreadyExists Error(Error_EntryAlreadyExists dafnyValue) {
    EntryAlreadyExists.Builder nativeBuilder = EntryAlreadyExists.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static EntryDoesNotExist Error(Error_EntryDoesNotExist dafnyValue) {
    EntryDoesNotExist.Builder nativeBuilder = EntryDoesNotExist.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfo Error(Error_InvalidAlgorithmSuiteInfo dafnyValue) {
    InvalidAlgorithmSuiteInfo.Builder nativeBuilder = InvalidAlgorithmSuiteInfo.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfoOnDecrypt Error(
      Error_InvalidAlgorithmSuiteInfoOnDecrypt dafnyValue) {
    InvalidAlgorithmSuiteInfoOnDecrypt.Builder nativeBuilder = InvalidAlgorithmSuiteInfoOnDecrypt.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidAlgorithmSuiteInfoOnEncrypt Error(
      Error_InvalidAlgorithmSuiteInfoOnEncrypt dafnyValue) {
    InvalidAlgorithmSuiteInfoOnEncrypt.Builder nativeBuilder = InvalidAlgorithmSuiteInfoOnEncrypt.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidDecryptionMaterials Error(Error_InvalidDecryptionMaterials dafnyValue) {
    InvalidDecryptionMaterials.Builder nativeBuilder = InvalidDecryptionMaterials.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidDecryptionMaterialsTransition Error(
      Error_InvalidDecryptionMaterialsTransition dafnyValue) {
    InvalidDecryptionMaterialsTransition.Builder nativeBuilder = InvalidDecryptionMaterialsTransition.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidEncryptionMaterials Error(Error_InvalidEncryptionMaterials dafnyValue) {
    InvalidEncryptionMaterials.Builder nativeBuilder = InvalidEncryptionMaterials.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static InvalidEncryptionMaterialsTransition Error(
      Error_InvalidEncryptionMaterialsTransition dafnyValue) {
    InvalidEncryptionMaterialsTransition.Builder nativeBuilder = InvalidEncryptionMaterialsTransition.builder();
    nativeBuilder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_AwsCryptographicMaterialProvidersException()) {
      return ToNative.Error((Error_AwsCryptographicMaterialProvidersException) dafnyValue);
    }
    if (dafnyValue.is_EntryAlreadyExists()) {
      return ToNative.Error((Error_EntryAlreadyExists) dafnyValue);
    }
    if (dafnyValue.is_EntryDoesNotExist()) {
      return ToNative.Error((Error_EntryDoesNotExist) dafnyValue);
    }
    if (dafnyValue.is_InvalidAlgorithmSuiteInfo()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfo) dafnyValue);
    }
    if (dafnyValue.is_InvalidAlgorithmSuiteInfoOnDecrypt()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfoOnDecrypt) dafnyValue);
    }
    if (dafnyValue.is_InvalidAlgorithmSuiteInfoOnEncrypt()) {
      return ToNative.Error((Error_InvalidAlgorithmSuiteInfoOnEncrypt) dafnyValue);
    }
    if (dafnyValue.is_InvalidDecryptionMaterials()) {
      return ToNative.Error((Error_InvalidDecryptionMaterials) dafnyValue);
    }
    if (dafnyValue.is_InvalidDecryptionMaterialsTransition()) {
      return ToNative.Error((Error_InvalidDecryptionMaterialsTransition) dafnyValue);
    }
    if (dafnyValue.is_InvalidEncryptionMaterials()) {
      return ToNative.Error((Error_InvalidEncryptionMaterials) dafnyValue);
    }
    if (dafnyValue.is_InvalidEncryptionMaterialsTransition()) {
      return ToNative.Error((Error_InvalidEncryptionMaterialsTransition) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    if (dafnyValue.is_AwsCryptographyPrimitives()) {
      return software.amazon.cryptography.primitives.ToNative.Error(dafnyValue.dtor_AwsCryptographyPrimitives());
    }
    if (dafnyValue.is_ComAmazonawsDynamodb()) {
      return software.amazon.cryptography.services.dynamodb.internaldafny.ToNative.Error(dafnyValue.dtor_ComAmazonawsDynamodb());
    }
    if (dafnyValue.is_ComAmazonawsKms()) {
      return software.amazon.cryptography.services.kms.internaldafny.ToNative.Error(dafnyValue.dtor_ComAmazonawsKms());
    }
    if (dafnyValue.is_AwsCryptographyKeyStore()) {
      return software.amazon.cryptography.keystore.ToNative.Error(dafnyValue.dtor_AwsCryptographyKeyStore());
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static AlgorithmSuiteInfo AlgorithmSuiteInfo(
      software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo dafnyValue) {
    AlgorithmSuiteInfo.Builder nativeBuilder = AlgorithmSuiteInfo.builder();
    nativeBuilder.id(ToNative.AlgorithmSuiteId(dafnyValue.dtor_id()));
    nativeBuilder.binaryId(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_binaryId()));
    nativeBuilder.messageVersion((dafnyValue.dtor_messageVersion()));
    nativeBuilder.encrypt(ToNative.Encrypt(dafnyValue.dtor_encrypt()));
    nativeBuilder.kdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_kdf()));
    nativeBuilder.commitment(ToNative.DerivationAlgorithm(dafnyValue.dtor_commitment()));
    nativeBuilder.signature(ToNative.SignatureAlgorithm(dafnyValue.dtor_signature()));
    nativeBuilder.symmetricSignature(ToNative.SymmetricSignatureAlgorithm(dafnyValue.dtor_symmetricSignature()));
    nativeBuilder.edkWrapping(ToNative.EdkWrappingAlgorithm(dafnyValue.dtor_edkWrapping()));
    return nativeBuilder.build();
  }

  public static BeaconKeyMaterials BeaconKeyMaterials(
      software.amazon.cryptography.materialproviders.internaldafny.types.BeaconKeyMaterials dafnyValue) {
    BeaconKeyMaterials.Builder nativeBuilder = BeaconKeyMaterials.builder();
    nativeBuilder.beaconKeyIdentifier(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_beaconKeyIdentifier()));
    if (dafnyValue.dtor_beaconKey().is_Some()) {
      nativeBuilder.beaconKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_beaconKey().dtor_value()));
    }
    if (dafnyValue.dtor_hmacKeys().is_Some()) {
      nativeBuilder.hmacKeys(ToNative.HmacKeyMap(dafnyValue.dtor_hmacKeys().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static BranchKeyMaterials BranchKeyMaterials(
      software.amazon.cryptography.materialproviders.internaldafny.types.BranchKeyMaterials dafnyValue) {
    BranchKeyMaterials.Builder nativeBuilder = BranchKeyMaterials.builder();
    nativeBuilder.branchKeyVersion(software.amazon.smithy.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static CreateAwsKmsDiscoveryKeyringInput CreateAwsKmsDiscoveryKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryKeyringInput dafnyValue) {
    CreateAwsKmsDiscoveryKeyringInput.Builder nativeBuilder = CreateAwsKmsDiscoveryKeyringInput.builder();
    nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsDiscoveryMultiKeyringInput CreateAwsKmsDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryMultiKeyringInput dafnyValue) {
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

  public static CreateAwsKmsHierarchicalKeyringInput CreateAwsKmsHierarchicalKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput dafnyValue) {
    CreateAwsKmsHierarchicalKeyringInput.Builder nativeBuilder = CreateAwsKmsHierarchicalKeyringInput.builder();
    if (dafnyValue.dtor_branchKeyId().is_Some()) {
      nativeBuilder.branchKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_branchKeyIdSupplier().is_Some()) {
      nativeBuilder.branchKeyIdSupplier(ToNative.BranchKeyIdSupplier(dafnyValue.dtor_branchKeyIdSupplier().dtor_value()));
    }
    nativeBuilder.keyStore(software.amazon.cryptography.keystore.ToNative.KeyStore(dafnyValue.dtor_keyStore()));
    nativeBuilder.ttlSeconds((dafnyValue.dtor_ttlSeconds()));
    if (dafnyValue.dtor_maxCacheSize().is_Some()) {
      nativeBuilder.maxCacheSize((dafnyValue.dtor_maxCacheSize().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsKeyringInput CreateAwsKmsKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput dafnyValue) {
    CreateAwsKmsKeyringInput.Builder nativeBuilder = CreateAwsKmsKeyringInput.builder();
    nativeBuilder.kmsKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkDiscoveryKeyringInput CreateAwsKmsMrkDiscoveryKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryKeyringInput dafnyValue) {
    CreateAwsKmsMrkDiscoveryKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkDiscoveryKeyringInput.builder();
    nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_discoveryFilter().is_Some()) {
      nativeBuilder.discoveryFilter(ToNative.DiscoveryFilter(dafnyValue.dtor_discoveryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    nativeBuilder.region(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_region()));
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkDiscoveryMultiKeyringInput CreateAwsKmsMrkDiscoveryMultiKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyValue) {
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

  public static CreateAwsKmsMrkKeyringInput CreateAwsKmsMrkKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput dafnyValue) {
    CreateAwsKmsMrkKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkKeyringInput.builder();
    nativeBuilder.kmsKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateAwsKmsMrkMultiKeyringInput CreateAwsKmsMrkMultiKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkMultiKeyringInput dafnyValue) {
    CreateAwsKmsMrkMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsMrkMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_generator().dtor_value()));
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

  public static CreateAwsKmsMultiKeyringInput CreateAwsKmsMultiKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMultiKeyringInput dafnyValue) {
    CreateAwsKmsMultiKeyringInput.Builder nativeBuilder = CreateAwsKmsMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_generator().dtor_value()));
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

  public static CreateAwsKmsRsaKeyringInput CreateAwsKmsRsaKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput dafnyValue) {
    CreateAwsKmsRsaKeyringInput.Builder nativeBuilder = CreateAwsKmsRsaKeyringInput.builder();
    if (dafnyValue.dtor_publicKey().is_Some()) {
      nativeBuilder.publicKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_publicKey().dtor_value()));
    }
    nativeBuilder.kmsKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyId()));
    nativeBuilder.encryptionAlgorithm(software.amazon.cryptography.services.kms.internaldafny.ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_encryptionAlgorithm()));
    if (dafnyValue.dtor_kmsClient().is_Some()) {
      nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateCryptographicMaterialsCacheInput CreateCryptographicMaterialsCacheInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateCryptographicMaterialsCacheInput dafnyValue) {
    CreateCryptographicMaterialsCacheInput.Builder nativeBuilder = CreateCryptographicMaterialsCacheInput.builder();
    nativeBuilder.entryCapacity((dafnyValue.dtor_entryCapacity()));
    if (dafnyValue.dtor_entryPruningTailSize().is_Some()) {
      nativeBuilder.entryPruningTailSize((dafnyValue.dtor_entryPruningTailSize().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateDefaultClientSupplierInput CreateDefaultClientSupplierInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput dafnyValue) {
    CreateDefaultClientSupplierInput.Builder nativeBuilder = CreateDefaultClientSupplierInput.builder();
    return nativeBuilder.build();
  }

  public static CreateDefaultCryptographicMaterialsManagerInput CreateDefaultCryptographicMaterialsManagerInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput dafnyValue) {
    CreateDefaultCryptographicMaterialsManagerInput.Builder nativeBuilder = CreateDefaultCryptographicMaterialsManagerInput.builder();
    nativeBuilder.keyring(ToNative.Keyring(dafnyValue.dtor_keyring()));
    return nativeBuilder.build();
  }

  public static CreateExpectedEncryptionContextCMMInput CreateExpectedEncryptionContextCMMInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateExpectedEncryptionContextCMMInput dafnyValue) {
    CreateExpectedEncryptionContextCMMInput.Builder nativeBuilder = CreateExpectedEncryptionContextCMMInput.builder();
    if (dafnyValue.dtor_underlyingCMM().is_Some()) {
      nativeBuilder.underlyingCMM(ToNative.CryptographicMaterialsManager(dafnyValue.dtor_underlyingCMM().dtor_value()));
    }
    if (dafnyValue.dtor_keyring().is_Some()) {
      nativeBuilder.keyring(ToNative.Keyring(dafnyValue.dtor_keyring().dtor_value()));
    }
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    return nativeBuilder.build();
  }

  public static CreateMultiKeyringInput CreateMultiKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput dafnyValue) {
    CreateMultiKeyringInput.Builder nativeBuilder = CreateMultiKeyringInput.builder();
    if (dafnyValue.dtor_generator().is_Some()) {
      nativeBuilder.generator(ToNative.Keyring(dafnyValue.dtor_generator().dtor_value()));
    }
    nativeBuilder.childKeyrings(ToNative.KeyringList(dafnyValue.dtor_childKeyrings()));
    return nativeBuilder.build();
  }

  public static CreateRawAesKeyringInput CreateRawAesKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput dafnyValue) {
    CreateRawAesKeyringInput.Builder nativeBuilder = CreateRawAesKeyringInput.builder();
    nativeBuilder.keyNamespace(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyNamespace()));
    nativeBuilder.keyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyName()));
    nativeBuilder.wrappingKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_wrappingKey()));
    nativeBuilder.wrappingAlg(ToNative.AesWrappingAlg(dafnyValue.dtor_wrappingAlg()));
    return nativeBuilder.build();
  }

  public static CreateRawRsaKeyringInput CreateRawRsaKeyringInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput dafnyValue) {
    CreateRawRsaKeyringInput.Builder nativeBuilder = CreateRawRsaKeyringInput.builder();
    nativeBuilder.keyNamespace(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyNamespace()));
    nativeBuilder.keyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyName()));
    nativeBuilder.paddingScheme(ToNative.PaddingScheme(dafnyValue.dtor_paddingScheme()));
    if (dafnyValue.dtor_publicKey().is_Some()) {
      nativeBuilder.publicKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_publicKey().dtor_value()));
    }
    if (dafnyValue.dtor_privateKey().is_Some()) {
      nativeBuilder.privateKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_privateKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DecryptionMaterials DecryptionMaterials(
      software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials dafnyValue) {
    DecryptionMaterials.Builder nativeBuilder = DecryptionMaterials.builder();
    nativeBuilder.algorithmSuite(ToNative.AlgorithmSuiteInfo(dafnyValue.dtor_algorithmSuite()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_plaintextDataKey().is_Some()) {
      nativeBuilder.plaintextDataKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_plaintextDataKey().dtor_value()));
    }
    if (dafnyValue.dtor_verificationKey().is_Some()) {
      nativeBuilder.verificationKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_verificationKey().dtor_value()));
    }
    if (dafnyValue.dtor_symmetricSigningKey().is_Some()) {
      nativeBuilder.symmetricSigningKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_symmetricSigningKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DecryptMaterialsInput DecryptMaterialsInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput dafnyValue) {
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

  public static DecryptMaterialsOutput DecryptMaterialsOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput dafnyValue) {
    DecryptMaterialsOutput.Builder nativeBuilder = DecryptMaterialsOutput.builder();
    nativeBuilder.decryptionMaterials(ToNative.DecryptionMaterials(dafnyValue.dtor_decryptionMaterials()));
    return nativeBuilder.build();
  }

  public static DeleteCacheEntryInput DeleteCacheEntryInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput dafnyValue) {
    DeleteCacheEntryInput.Builder nativeBuilder = DeleteCacheEntryInput.builder();
    nativeBuilder.identifier(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_identifier()));
    return nativeBuilder.build();
  }

  public static DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING(DIRECT__KEY__WRAPPING dafnyValue) {
    DIRECT_KEY_WRAPPING.Builder nativeBuilder = DIRECT_KEY_WRAPPING.builder();
    return nativeBuilder.build();
  }

  public static DiscoveryFilter DiscoveryFilter(
      software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter dafnyValue) {
    DiscoveryFilter.Builder nativeBuilder = DiscoveryFilter.builder();
    nativeBuilder.accountIds(ToNative.AccountIdList(dafnyValue.dtor_accountIds()));
    nativeBuilder.partition(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_partition()));
    return nativeBuilder.build();
  }

  public static ECDSA ECDSA(
      software.amazon.cryptography.materialproviders.internaldafny.types.ECDSA dafnyValue) {
    ECDSA.Builder nativeBuilder = ECDSA.builder();
    nativeBuilder.curve(software.amazon.cryptography.primitives.ToNative.ECDSASignatureAlgorithm(dafnyValue.dtor_curve()));
    return nativeBuilder.build();
  }

  public static EncryptedDataKey EncryptedDataKey(
      software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey dafnyValue) {
    EncryptedDataKey.Builder nativeBuilder = EncryptedDataKey.builder();
    nativeBuilder.keyProviderId(software.amazon.smithy.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_keyProviderId()));
    nativeBuilder.keyProviderInfo(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_keyProviderInfo()));
    nativeBuilder.ciphertext(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_ciphertext()));
    return nativeBuilder.build();
  }

  public static EncryptionMaterials EncryptionMaterials(
      software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials dafnyValue) {
    EncryptionMaterials.Builder nativeBuilder = EncryptionMaterials.builder();
    nativeBuilder.algorithmSuite(ToNative.AlgorithmSuiteInfo(dafnyValue.dtor_algorithmSuite()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.encryptedDataKeys(ToNative.EncryptedDataKeyList(dafnyValue.dtor_encryptedDataKeys()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_plaintextDataKey().is_Some()) {
      nativeBuilder.plaintextDataKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_plaintextDataKey().dtor_value()));
    }
    if (dafnyValue.dtor_signingKey().is_Some()) {
      nativeBuilder.signingKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_signingKey().dtor_value()));
    }
    if (dafnyValue.dtor_symmetricSigningKeys().is_Some()) {
      nativeBuilder.symmetricSigningKeys(ToNative.SymmetricSigningKeyList(dafnyValue.dtor_symmetricSigningKeys().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ByteBuffer GetAlgorithmSuiteInfoInput(DafnySequence<? extends Byte> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue);
  }

  public static GetBranchKeyIdInput GetBranchKeyIdInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdInput dafnyValue) {
    GetBranchKeyIdInput.Builder nativeBuilder = GetBranchKeyIdInput.builder();
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    return nativeBuilder.build();
  }

  public static GetBranchKeyIdOutput GetBranchKeyIdOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput dafnyValue) {
    GetBranchKeyIdOutput.Builder nativeBuilder = GetBranchKeyIdOutput.builder();
    nativeBuilder.branchKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyId()));
    return nativeBuilder.build();
  }

  public static GetCacheEntryInput GetCacheEntryInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput dafnyValue) {
    GetCacheEntryInput.Builder nativeBuilder = GetCacheEntryInput.builder();
    nativeBuilder.identifier(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_identifier()));
    if (dafnyValue.dtor_bytesUsed().is_Some()) {
      nativeBuilder.bytesUsed((dafnyValue.dtor_bytesUsed().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetCacheEntryOutput GetCacheEntryOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput dafnyValue) {
    GetCacheEntryOutput.Builder nativeBuilder = GetCacheEntryOutput.builder();
    nativeBuilder.materials(ToNative.Materials(dafnyValue.dtor_materials()));
    nativeBuilder.creationTime((dafnyValue.dtor_creationTime()));
    nativeBuilder.expiryTime((dafnyValue.dtor_expiryTime()));
    nativeBuilder.messagesUsed((dafnyValue.dtor_messagesUsed()));
    nativeBuilder.bytesUsed((dafnyValue.dtor_bytesUsed()));
    return nativeBuilder.build();
  }

  public static GetClientInput GetClientInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput dafnyValue) {
    GetClientInput.Builder nativeBuilder = GetClientInput.builder();
    nativeBuilder.region(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_region()));
    return nativeBuilder.build();
  }

  public static GetEncryptionMaterialsInput GetEncryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput dafnyValue) {
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

  public static GetEncryptionMaterialsOutput GetEncryptionMaterialsOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput dafnyValue) {
    GetEncryptionMaterialsOutput.Builder nativeBuilder = GetEncryptionMaterialsOutput.builder();
    nativeBuilder.encryptionMaterials(ToNative.EncryptionMaterials(dafnyValue.dtor_encryptionMaterials()));
    return nativeBuilder.build();
  }

  public static HKDF HKDF(
      software.amazon.cryptography.materialproviders.internaldafny.types.HKDF dafnyValue) {
    HKDF.Builder nativeBuilder = HKDF.builder();
    nativeBuilder.hmac(software.amazon.cryptography.primitives.ToNative.DigestAlgorithm(dafnyValue.dtor_hmac()));
    nativeBuilder.saltLength((dafnyValue.dtor_saltLength()));
    nativeBuilder.inputKeyLength((dafnyValue.dtor_inputKeyLength()));
    nativeBuilder.outputKeyLength((dafnyValue.dtor_outputKeyLength()));
    return nativeBuilder.build();
  }

  public static IDENTITY IDENTITY(
      software.amazon.cryptography.materialproviders.internaldafny.types.IDENTITY dafnyValue) {
    IDENTITY.Builder nativeBuilder = IDENTITY.builder();
    return nativeBuilder.build();
  }

  public static InitializeDecryptionMaterialsInput InitializeDecryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput dafnyValue) {
    InitializeDecryptionMaterialsInput.Builder nativeBuilder = InitializeDecryptionMaterialsInput.builder();
    nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    return nativeBuilder.build();
  }

  public static InitializeEncryptionMaterialsInput InitializeEncryptionMaterialsInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput dafnyValue) {
    InitializeEncryptionMaterialsInput.Builder nativeBuilder = InitializeEncryptionMaterialsInput.builder();
    nativeBuilder.algorithmSuiteId(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithmSuiteId()));
    nativeBuilder.encryptionContext(ToNative.EncryptionContext(dafnyValue.dtor_encryptionContext()));
    nativeBuilder.requiredEncryptionContextKeys(ToNative.EncryptionContextKeys(dafnyValue.dtor_requiredEncryptionContextKeys()));
    if (dafnyValue.dtor_signingKey().is_Some()) {
      nativeBuilder.signingKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_signingKey().dtor_value()));
    }
    if (dafnyValue.dtor_verificationKey().is_Some()) {
      nativeBuilder.verificationKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_verificationKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static IntermediateKeyWrapping IntermediateKeyWrapping(
      software.amazon.cryptography.materialproviders.internaldafny.types.IntermediateKeyWrapping dafnyValue) {
    IntermediateKeyWrapping.Builder nativeBuilder = IntermediateKeyWrapping.builder();
    nativeBuilder.keyEncryptionKeyKdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_keyEncryptionKeyKdf()));
    nativeBuilder.macKeyKdf(ToNative.DerivationAlgorithm(dafnyValue.dtor_macKeyKdf()));
    nativeBuilder.pdkEncryptAlgorithm(ToNative.Encrypt(dafnyValue.dtor_pdkEncryptAlgorithm()));
    return nativeBuilder.build();
  }

  public static MaterialProvidersConfig MaterialProvidersConfig(
      software.amazon.cryptography.materialproviders.internaldafny.types.MaterialProvidersConfig dafnyValue) {
    MaterialProvidersConfig.Builder nativeBuilder = MaterialProvidersConfig.builder();
    return nativeBuilder.build();
  }

  public static None None(
      software.amazon.cryptography.materialproviders.internaldafny.types.None dafnyValue) {
    None.Builder nativeBuilder = None.builder();
    return nativeBuilder.build();
  }

  public static OnDecryptInput OnDecryptInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput dafnyValue) {
    OnDecryptInput.Builder nativeBuilder = OnDecryptInput.builder();
    nativeBuilder.materials(ToNative.DecryptionMaterials(dafnyValue.dtor_materials()));
    nativeBuilder.encryptedDataKeys(ToNative.EncryptedDataKeyList(dafnyValue.dtor_encryptedDataKeys()));
    return nativeBuilder.build();
  }

  public static OnDecryptOutput OnDecryptOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput dafnyValue) {
    OnDecryptOutput.Builder nativeBuilder = OnDecryptOutput.builder();
    nativeBuilder.materials(ToNative.DecryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static OnEncryptInput OnEncryptInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput dafnyValue) {
    OnEncryptInput.Builder nativeBuilder = OnEncryptInput.builder();
    nativeBuilder.materials(ToNative.EncryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static OnEncryptOutput OnEncryptOutput(
      software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput dafnyValue) {
    OnEncryptOutput.Builder nativeBuilder = OnEncryptOutput.builder();
    nativeBuilder.materials(ToNative.EncryptionMaterials(dafnyValue.dtor_materials()));
    return nativeBuilder.build();
  }

  public static PutCacheEntryInput PutCacheEntryInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput dafnyValue) {
    PutCacheEntryInput.Builder nativeBuilder = PutCacheEntryInput.builder();
    nativeBuilder.identifier(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_identifier()));
    nativeBuilder.materials(ToNative.Materials(dafnyValue.dtor_materials()));
    nativeBuilder.creationTime((dafnyValue.dtor_creationTime()));
    nativeBuilder.expiryTime((dafnyValue.dtor_expiryTime()));
    if (dafnyValue.dtor_messagesUsed().is_Some()) {
      nativeBuilder.messagesUsed((dafnyValue.dtor_messagesUsed().dtor_value()));
    }
    if (dafnyValue.dtor_bytesUsed().is_Some()) {
      nativeBuilder.bytesUsed((dafnyValue.dtor_bytesUsed().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdaterUsageMetadataInput UpdaterUsageMetadataInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.UpdaterUsageMetadataInput dafnyValue) {
    UpdaterUsageMetadataInput.Builder nativeBuilder = UpdaterUsageMetadataInput.builder();
    nativeBuilder.identifier(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_identifier()));
    nativeBuilder.bytesUsed((dafnyValue.dtor_bytesUsed()));
    return nativeBuilder.build();
  }

  public static ValidateCommitmentPolicyOnDecryptInput ValidateCommitmentPolicyOnDecryptInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnDecryptInput dafnyValue) {
    ValidateCommitmentPolicyOnDecryptInput.Builder nativeBuilder = ValidateCommitmentPolicyOnDecryptInput.builder();
    nativeBuilder.algorithm(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithm()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    return nativeBuilder.build();
  }

  public static ValidateCommitmentPolicyOnEncryptInput ValidateCommitmentPolicyOnEncryptInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnEncryptInput dafnyValue) {
    ValidateCommitmentPolicyOnEncryptInput.Builder nativeBuilder = ValidateCommitmentPolicyOnEncryptInput.builder();
    nativeBuilder.algorithm(ToNative.AlgorithmSuiteId(dafnyValue.dtor_algorithm()));
    nativeBuilder.commitmentPolicy(ToNative.CommitmentPolicy(dafnyValue.dtor_commitmentPolicy()));
    return nativeBuilder.build();
  }

  public static ValidDecryptionMaterialsTransitionInput ValidDecryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.ValidDecryptionMaterialsTransitionInput dafnyValue) {
    ValidDecryptionMaterialsTransitionInput.Builder nativeBuilder = ValidDecryptionMaterialsTransitionInput.builder();
    nativeBuilder.start(ToNative.DecryptionMaterials(dafnyValue.dtor_start()));
    nativeBuilder.stop(ToNative.DecryptionMaterials(dafnyValue.dtor_stop()));
    return nativeBuilder.build();
  }

  public static ValidEncryptionMaterialsTransitionInput ValidEncryptionMaterialsTransitionInput(
      software.amazon.cryptography.materialproviders.internaldafny.types.ValidEncryptionMaterialsTransitionInput dafnyValue) {
    ValidEncryptionMaterialsTransitionInput.Builder nativeBuilder = ValidEncryptionMaterialsTransitionInput.builder();
    nativeBuilder.start(ToNative.EncryptionMaterials(dafnyValue.dtor_start()));
    nativeBuilder.stop(ToNative.EncryptionMaterials(dafnyValue.dtor_stop()));
    return nativeBuilder.build();
  }

  public static AesWrappingAlg AesWrappingAlg(
      software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg dafnyValue) {
    if (dafnyValue.is_ALG__AES128__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
    }
    if (dafnyValue.is_ALG__AES192__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
    }
    if (dafnyValue.is_ALG__AES256__GCM__IV12__TAG16()) {
      return AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.AesWrappingAlg matches the input : " + dafnyValue);
  }

  public static DBEAlgorithmSuiteId DBEAlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId dafnyValue) {
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384()) {
      return DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384;
    }
    if (dafnyValue.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384()) {
      return DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.DBEAlgorithmSuiteId matches the input : " + dafnyValue);
  }

  public static DBECommitmentPolicy DBECommitmentPolicy(
      software.amazon.cryptography.materialproviders.internaldafny.types.DBECommitmentPolicy dafnyValue) {
    if (dafnyValue.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT()) {
      return DBECommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.DBECommitmentPolicy matches the input : " + dafnyValue);
  }

  public static ESDKAlgorithmSuiteId ESDKAlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId dafnyValue) {
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
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.ESDKAlgorithmSuiteId matches the input : " + dafnyValue);
  }

  public static ESDKCommitmentPolicy ESDKCommitmentPolicy(
      software.amazon.cryptography.materialproviders.internaldafny.types.ESDKCommitmentPolicy dafnyValue) {
    if (dafnyValue.is_FORBID__ENCRYPT__ALLOW__DECRYPT()) {
      return ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
    }
    if (dafnyValue.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT()) {
      return ESDKCommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
    }
    if (dafnyValue.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT()) {
      return ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.ESDKCommitmentPolicy matches the input : " + dafnyValue);
  }

  public static PaddingScheme PaddingScheme(
      software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme dafnyValue) {
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
    throw new IllegalArgumentException("No entry of software.amazon.cryptography.materialproviders.model.PaddingScheme matches the input : " + dafnyValue);
  }

  public static AlgorithmSuiteId AlgorithmSuiteId(
      software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId dafnyValue) {
    AlgorithmSuiteId.Builder nativeBuilder = AlgorithmSuiteId.builder();
    if (dafnyValue.is_ESDK()) {
      nativeBuilder.ESDK(ToNative.ESDKAlgorithmSuiteId(dafnyValue.dtor_ESDK()));
    }
    if (dafnyValue.is_DBE()) {
      nativeBuilder.DBE(ToNative.DBEAlgorithmSuiteId(dafnyValue.dtor_DBE()));
    }
    return nativeBuilder.build();
  }

  public static CommitmentPolicy CommitmentPolicy(
      software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy dafnyValue) {
    CommitmentPolicy.Builder nativeBuilder = CommitmentPolicy.builder();
    if (dafnyValue.is_ESDK()) {
      nativeBuilder.ESDK(ToNative.ESDKCommitmentPolicy(dafnyValue.dtor_ESDK()));
    }
    if (dafnyValue.is_DBE()) {
      nativeBuilder.DBE(ToNative.DBECommitmentPolicy(dafnyValue.dtor_DBE()));
    }
    return nativeBuilder.build();
  }

  public static DerivationAlgorithm DerivationAlgorithm(
      software.amazon.cryptography.materialproviders.internaldafny.types.DerivationAlgorithm dafnyValue) {
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

  public static EdkWrappingAlgorithm EdkWrappingAlgorithm(
      software.amazon.cryptography.materialproviders.internaldafny.types.EdkWrappingAlgorithm dafnyValue) {
    EdkWrappingAlgorithm.Builder nativeBuilder = EdkWrappingAlgorithm.builder();
    if (dafnyValue.is_DIRECT__KEY__WRAPPING()) {
      nativeBuilder.DIRECT_KEY_WRAPPING(ToNative.DIRECT_KEY_WRAPPING(dafnyValue.dtor_DIRECT__KEY__WRAPPING()));
    }
    if (dafnyValue.is_IntermediateKeyWrapping()) {
      nativeBuilder.IntermediateKeyWrapping(ToNative.IntermediateKeyWrapping(dafnyValue.dtor_IntermediateKeyWrapping()));
    }
    return nativeBuilder.build();
  }

  public static Encrypt Encrypt(
      software.amazon.cryptography.materialproviders.internaldafny.types.Encrypt dafnyValue) {
    Encrypt.Builder nativeBuilder = Encrypt.builder();
    if (dafnyValue.is_AES__GCM()) {
      nativeBuilder.AES_GCM(software.amazon.cryptography.primitives.ToNative.AES_GCM(dafnyValue.dtor_AES__GCM()));
    }
    return nativeBuilder.build();
  }

  public static Materials Materials(
      software.amazon.cryptography.materialproviders.internaldafny.types.Materials dafnyValue) {
    Materials.Builder nativeBuilder = Materials.builder();
    if (dafnyValue.is_Encryption()) {
      nativeBuilder.Encryption(ToNative.EncryptionMaterials(dafnyValue.dtor_Encryption()));
    }
    if (dafnyValue.is_Decryption()) {
      nativeBuilder.Decryption(ToNative.DecryptionMaterials(dafnyValue.dtor_Decryption()));
    }
    if (dafnyValue.is_BranchKey()) {
      nativeBuilder.BranchKey(ToNative.BranchKeyMaterials(dafnyValue.dtor_BranchKey()));
    }
    if (dafnyValue.is_BeaconKey()) {
      nativeBuilder.BeaconKey(ToNative.BeaconKeyMaterials(dafnyValue.dtor_BeaconKey()));
    }
    return nativeBuilder.build();
  }

  public static SignatureAlgorithm SignatureAlgorithm(
      software.amazon.cryptography.materialproviders.internaldafny.types.SignatureAlgorithm dafnyValue) {
    SignatureAlgorithm.Builder nativeBuilder = SignatureAlgorithm.builder();
    if (dafnyValue.is_ECDSA()) {
      nativeBuilder.ECDSA(ToNative.ECDSA(dafnyValue.dtor_ECDSA()));
    }
    if (dafnyValue.is_None()) {
      nativeBuilder.None(ToNative.None(dafnyValue.dtor_None()));
    }
    return nativeBuilder.build();
  }

  public static SymmetricSignatureAlgorithm SymmetricSignatureAlgorithm(
      software.amazon.cryptography.materialproviders.internaldafny.types.SymmetricSignatureAlgorithm dafnyValue) {
    SymmetricSignatureAlgorithm.Builder nativeBuilder = SymmetricSignatureAlgorithm.builder();
    if (dafnyValue.is_HMAC()) {
      nativeBuilder.HMAC(software.amazon.cryptography.primitives.ToNative.DigestAlgorithm(dafnyValue.dtor_HMAC()));
    }
    if (dafnyValue.is_None()) {
      nativeBuilder.None(ToNative.None(dafnyValue.dtor_None()));
    }
    return nativeBuilder.build();
  }

  public static List<String> AccountIdList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<EncryptedDataKey> EncryptedDataKeyList(
      DafnySequence<? extends software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.materialproviders.ToNative::EncryptedDataKey);
  }

  public static List<String> EncryptionContextKeys(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes);
  }

  public static List<String> GrantTokenList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<IKeyring> KeyringList(
      DafnySequence<? extends software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.materialproviders.ToNative::Keyring);
  }

  public static List<String> KmsKeyIdList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> RegionList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<ByteBuffer> SymmetricSigningKeyList(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::ByteBuffer);
  }

  public static Map<String, String> EncryptionContext(
      DafnyMap<? extends DafnySequence<? extends Byte>, ? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes);
  }

  public static Map<String, ByteBuffer> HmacKeyMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::ByteBuffer);
  }

  public static IBranchKeyIdSupplier BranchKeyIdSupplier(
      software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier dafnyValue) {
    if (dafnyValue instanceof BranchKeyIdSupplier.NativeWrapper) {
      return ((BranchKeyIdSupplier.NativeWrapper) dafnyValue)._impl;
    }
    return BranchKeyIdSupplier.wrap(dafnyValue);
  }

  public static IClientSupplier ClientSupplier(
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier dafnyValue) {
    if (dafnyValue instanceof ClientSupplier.NativeWrapper) {
      return ((ClientSupplier.NativeWrapper) dafnyValue)._impl;
    }
    return ClientSupplier.wrap(dafnyValue);
  }

  public static ICryptographicMaterialsCache CryptographicMaterialsCache(
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache dafnyValue) {
    if (dafnyValue instanceof CryptographicMaterialsCache.NativeWrapper) {
      return ((CryptographicMaterialsCache.NativeWrapper) dafnyValue)._impl;
    }
    return CryptographicMaterialsCache.wrap(dafnyValue);
  }

  public static ICryptographicMaterialsManager CryptographicMaterialsManager(
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager dafnyValue) {
    if (dafnyValue instanceof CryptographicMaterialsManager.NativeWrapper) {
      return ((CryptographicMaterialsManager.NativeWrapper) dafnyValue)._impl;
    }
    return CryptographicMaterialsManager.wrap(dafnyValue);
  }

  public static IKeyring Keyring(
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring dafnyValue) {
    if (dafnyValue instanceof Keyring.NativeWrapper) {
      return ((Keyring.NativeWrapper) dafnyValue)._impl;
    }
    return Keyring.wrap(dafnyValue);
  }

  public static MaterialProviders AwsCryptographicMaterialProviders(
      IAwsCryptographicMaterialProvidersClient dafnyValue) {
    return new MaterialProviders(dafnyValue);
  }
}
