// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package Dafny.Com.Amazonaws.Kms;

import Dafny.Com.Amazonaws.Kms.Types.Error_AlreadyExistsException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CloudHsmClusterInUseException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CloudHsmClusterInvalidConfigurationException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CloudHsmClusterNotActiveException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CloudHsmClusterNotFoundException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CloudHsmClusterNotRelatedException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CustomKeyStoreHasCMKsException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CustomKeyStoreInvalidStateException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CustomKeyStoreNameInUseException;
import Dafny.Com.Amazonaws.Kms.Types.Error_CustomKeyStoreNotFoundException;
import Dafny.Com.Amazonaws.Kms.Types.Error_DependencyTimeoutException;
import Dafny.Com.Amazonaws.Kms.Types.Error_DisabledException;
import Dafny.Com.Amazonaws.Kms.Types.Error_ExpiredImportTokenException;
import Dafny.Com.Amazonaws.Kms.Types.Error_IncorrectKeyException;
import Dafny.Com.Amazonaws.Kms.Types.Error_IncorrectKeyMaterialException;
import Dafny.Com.Amazonaws.Kms.Types.Error_IncorrectTrustAnchorException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidAliasNameException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidArnException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidCiphertextException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidGrantIdException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidGrantTokenException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidImportTokenException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidKeyUsageException;
import Dafny.Com.Amazonaws.Kms.Types.Error_InvalidMarkerException;
import Dafny.Com.Amazonaws.Kms.Types.Error_KMSInternalException;
import Dafny.Com.Amazonaws.Kms.Types.Error_KMSInvalidSignatureException;
import Dafny.Com.Amazonaws.Kms.Types.Error_KMSInvalidStateException;
import Dafny.Com.Amazonaws.Kms.Types.Error_KeyUnavailableException;
import Dafny.Com.Amazonaws.Kms.Types.Error_LimitExceededException;
import Dafny.Com.Amazonaws.Kms.Types.Error_MalformedPolicyDocumentException;
import Dafny.Com.Amazonaws.Kms.Types.Error_NotFoundException;
import Dafny.Com.Amazonaws.Kms.Types.Error_TagException;
import Dafny.Com.Amazonaws.Kms.Types.Error_UnsupportedOperationException;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Character;
import java.lang.String;
import java.util.List;
import java.util.Map;
import software.amazon.awssdk.core.SdkBytes;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.model.AlgorithmSpec;
import software.amazon.awssdk.services.kms.model.AliasListEntry;
import software.amazon.awssdk.services.kms.model.AlreadyExistsException;
import software.amazon.awssdk.services.kms.model.CancelKeyDeletionRequest;
import software.amazon.awssdk.services.kms.model.CancelKeyDeletionResponse;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterInUseException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterInvalidConfigurationException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotActiveException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotFoundException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotRelatedException;
import software.amazon.awssdk.services.kms.model.ConnectCustomKeyStoreRequest;
import software.amazon.awssdk.services.kms.model.ConnectCustomKeyStoreResponse;
import software.amazon.awssdk.services.kms.model.ConnectionErrorCodeType;
import software.amazon.awssdk.services.kms.model.ConnectionStateType;
import software.amazon.awssdk.services.kms.model.CreateAliasRequest;
import software.amazon.awssdk.services.kms.model.CreateCustomKeyStoreRequest;
import software.amazon.awssdk.services.kms.model.CreateCustomKeyStoreResponse;
import software.amazon.awssdk.services.kms.model.CreateGrantRequest;
import software.amazon.awssdk.services.kms.model.CreateGrantResponse;
import software.amazon.awssdk.services.kms.model.CreateKeyRequest;
import software.amazon.awssdk.services.kms.model.CreateKeyResponse;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreHasCmKsException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreInvalidStateException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreNameInUseException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreNotFoundException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoresListEntry;
import software.amazon.awssdk.services.kms.model.CustomerMasterKeySpec;
import software.amazon.awssdk.services.kms.model.DataKeyPairSpec;
import software.amazon.awssdk.services.kms.model.DataKeySpec;
import software.amazon.awssdk.services.kms.model.DecryptRequest;
import software.amazon.awssdk.services.kms.model.DecryptResponse;
import software.amazon.awssdk.services.kms.model.DeleteAliasRequest;
import software.amazon.awssdk.services.kms.model.DeleteCustomKeyStoreRequest;
import software.amazon.awssdk.services.kms.model.DeleteCustomKeyStoreResponse;
import software.amazon.awssdk.services.kms.model.DeleteImportedKeyMaterialRequest;
import software.amazon.awssdk.services.kms.model.DependencyTimeoutException;
import software.amazon.awssdk.services.kms.model.DescribeCustomKeyStoresRequest;
import software.amazon.awssdk.services.kms.model.DescribeCustomKeyStoresResponse;
import software.amazon.awssdk.services.kms.model.DescribeKeyRequest;
import software.amazon.awssdk.services.kms.model.DescribeKeyResponse;
import software.amazon.awssdk.services.kms.model.DisableKeyRequest;
import software.amazon.awssdk.services.kms.model.DisableKeyRotationRequest;
import software.amazon.awssdk.services.kms.model.DisabledException;
import software.amazon.awssdk.services.kms.model.DisconnectCustomKeyStoreRequest;
import software.amazon.awssdk.services.kms.model.DisconnectCustomKeyStoreResponse;
import software.amazon.awssdk.services.kms.model.EnableKeyRequest;
import software.amazon.awssdk.services.kms.model.EnableKeyRotationRequest;
import software.amazon.awssdk.services.kms.model.EncryptRequest;
import software.amazon.awssdk.services.kms.model.EncryptResponse;
import software.amazon.awssdk.services.kms.model.EncryptionAlgorithmSpec;
import software.amazon.awssdk.services.kms.model.ExpirationModelType;
import software.amazon.awssdk.services.kms.model.ExpiredImportTokenException;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyPairRequest;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyPairResponse;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyPairWithoutPlaintextRequest;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyPairWithoutPlaintextResponse;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyRequest;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyResponse;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyWithoutPlaintextRequest;
import software.amazon.awssdk.services.kms.model.GenerateDataKeyWithoutPlaintextResponse;
import software.amazon.awssdk.services.kms.model.GenerateRandomRequest;
import software.amazon.awssdk.services.kms.model.GenerateRandomResponse;
import software.amazon.awssdk.services.kms.model.GetKeyPolicyRequest;
import software.amazon.awssdk.services.kms.model.GetKeyPolicyResponse;
import software.amazon.awssdk.services.kms.model.GetKeyRotationStatusRequest;
import software.amazon.awssdk.services.kms.model.GetKeyRotationStatusResponse;
import software.amazon.awssdk.services.kms.model.GetParametersForImportRequest;
import software.amazon.awssdk.services.kms.model.GetParametersForImportResponse;
import software.amazon.awssdk.services.kms.model.GetPublicKeyRequest;
import software.amazon.awssdk.services.kms.model.GetPublicKeyResponse;
import software.amazon.awssdk.services.kms.model.GrantConstraints;
import software.amazon.awssdk.services.kms.model.GrantListEntry;
import software.amazon.awssdk.services.kms.model.GrantOperation;
import software.amazon.awssdk.services.kms.model.ImportKeyMaterialRequest;
import software.amazon.awssdk.services.kms.model.ImportKeyMaterialResponse;
import software.amazon.awssdk.services.kms.model.IncorrectKeyException;
import software.amazon.awssdk.services.kms.model.IncorrectKeyMaterialException;
import software.amazon.awssdk.services.kms.model.IncorrectTrustAnchorException;
import software.amazon.awssdk.services.kms.model.InvalidAliasNameException;
import software.amazon.awssdk.services.kms.model.InvalidArnException;
import software.amazon.awssdk.services.kms.model.InvalidCiphertextException;
import software.amazon.awssdk.services.kms.model.InvalidGrantIdException;
import software.amazon.awssdk.services.kms.model.InvalidGrantTokenException;
import software.amazon.awssdk.services.kms.model.InvalidImportTokenException;
import software.amazon.awssdk.services.kms.model.InvalidKeyUsageException;
import software.amazon.awssdk.services.kms.model.InvalidMarkerException;
import software.amazon.awssdk.services.kms.model.KeyManagerType;
import software.amazon.awssdk.services.kms.model.KeyMetadata;
import software.amazon.awssdk.services.kms.model.KeySpec;
import software.amazon.awssdk.services.kms.model.KeyState;
import software.amazon.awssdk.services.kms.model.KeyUnavailableException;
import software.amazon.awssdk.services.kms.model.KeyUsageType;
import software.amazon.awssdk.services.kms.model.KmsInternalException;
import software.amazon.awssdk.services.kms.model.KmsInvalidSignatureException;
import software.amazon.awssdk.services.kms.model.KmsInvalidStateException;
import software.amazon.awssdk.services.kms.model.LimitExceededException;
import software.amazon.awssdk.services.kms.model.ListAliasesRequest;
import software.amazon.awssdk.services.kms.model.ListAliasesResponse;
import software.amazon.awssdk.services.kms.model.ListGrantsRequest;
import software.amazon.awssdk.services.kms.model.ListGrantsResponse;
import software.amazon.awssdk.services.kms.model.ListKeyPoliciesRequest;
import software.amazon.awssdk.services.kms.model.ListKeyPoliciesResponse;
import software.amazon.awssdk.services.kms.model.ListResourceTagsRequest;
import software.amazon.awssdk.services.kms.model.ListResourceTagsResponse;
import software.amazon.awssdk.services.kms.model.MalformedPolicyDocumentException;
import software.amazon.awssdk.services.kms.model.MessageType;
import software.amazon.awssdk.services.kms.model.MultiRegionConfiguration;
import software.amazon.awssdk.services.kms.model.MultiRegionKey;
import software.amazon.awssdk.services.kms.model.MultiRegionKeyType;
import software.amazon.awssdk.services.kms.model.NotFoundException;
import software.amazon.awssdk.services.kms.model.OriginType;
import software.amazon.awssdk.services.kms.model.PutKeyPolicyRequest;
import software.amazon.awssdk.services.kms.model.ReEncryptRequest;
import software.amazon.awssdk.services.kms.model.ReEncryptResponse;
import software.amazon.awssdk.services.kms.model.ReplicateKeyRequest;
import software.amazon.awssdk.services.kms.model.ReplicateKeyResponse;
import software.amazon.awssdk.services.kms.model.RetireGrantRequest;
import software.amazon.awssdk.services.kms.model.RevokeGrantRequest;
import software.amazon.awssdk.services.kms.model.ScheduleKeyDeletionRequest;
import software.amazon.awssdk.services.kms.model.ScheduleKeyDeletionResponse;
import software.amazon.awssdk.services.kms.model.SignRequest;
import software.amazon.awssdk.services.kms.model.SignResponse;
import software.amazon.awssdk.services.kms.model.SigningAlgorithmSpec;
import software.amazon.awssdk.services.kms.model.Tag;
import software.amazon.awssdk.services.kms.model.TagException;
import software.amazon.awssdk.services.kms.model.TagResourceRequest;
import software.amazon.awssdk.services.kms.model.UnsupportedOperationException;
import software.amazon.awssdk.services.kms.model.UntagResourceRequest;
import software.amazon.awssdk.services.kms.model.UpdateAliasRequest;
import software.amazon.awssdk.services.kms.model.UpdateCustomKeyStoreRequest;
import software.amazon.awssdk.services.kms.model.UpdateCustomKeyStoreResponse;
import software.amazon.awssdk.services.kms.model.UpdateKeyDescriptionRequest;
import software.amazon.awssdk.services.kms.model.UpdatePrimaryRegionRequest;
import software.amazon.awssdk.services.kms.model.VerifyRequest;
import software.amazon.awssdk.services.kms.model.VerifyResponse;
import software.amazon.awssdk.services.kms.model.WrappingKeySpec;

public class ToNative {
  public static CancelKeyDeletionRequest CancelKeyDeletionRequest(
      Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionRequest dafnyValue) {
    CancelKeyDeletionRequest.Builder builder = CancelKeyDeletionRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static ConnectCustomKeyStoreRequest ConnectCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreRequest dafnyValue) {
    ConnectCustomKeyStoreRequest.Builder builder = ConnectCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static CreateAliasRequest CreateAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateAliasRequest dafnyValue) {
    CreateAliasRequest.Builder builder = CreateAliasRequest.builder();
    builder.aliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    builder.targetKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return builder.build();
  }

  public static CreateCustomKeyStoreRequest CreateCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreRequest dafnyValue) {
    CreateCustomKeyStoreRequest.Builder builder = CreateCustomKeyStoreRequest.builder();
    builder.customKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName()));
    builder.cloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId()));
    builder.trustAnchorCertificate(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TrustAnchorCertificate()));
    builder.keyStorePassword(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword()));
    return builder.build();
  }

  public static CreateGrantRequest CreateGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateGrantRequest dafnyValue) {
    CreateGrantRequest.Builder builder = CreateGrantRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.granteePrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal()));
    if (dafnyValue.dtor_RetiringPrincipal().is_Some()) {
      builder.retiringPrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RetiringPrincipal().dtor_value()));
    }
    builder.operations(ToNative.GrantOperationList(dafnyValue.dtor_Operations()));
    if (dafnyValue.dtor_Constraints().is_Some()) {
      builder.constraints(ToNative.GrantConstraints(dafnyValue.dtor_Constraints().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_Name().is_Some()) {
      builder.name(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Name().dtor_value()));
    }
    return builder.build();
  }

  public static CreateKeyRequest CreateKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateKeyRequest dafnyValue) {
    CreateKeyRequest.Builder builder = CreateKeyRequest.builder();
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_Origin().is_Some()) {
      builder.origin(ToNative.OriginType(dafnyValue.dtor_Origin().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegion().is_Some()) {
      builder.multiRegion((dafnyValue.dtor_MultiRegion().dtor_value()));
    }
    return builder.build();
  }

  public static DecryptRequest DecryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.DecryptRequest dafnyValue) {
    DecryptRequest.Builder builder = DecryptRequest.builder();
    builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().toRawArray())));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static DeleteAliasRequest DeleteAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteAliasRequest dafnyValue) {
    DeleteAliasRequest.Builder builder = DeleteAliasRequest.builder();
    builder.aliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    return builder.build();
  }

  public static DeleteCustomKeyStoreRequest DeleteCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreRequest dafnyValue) {
    DeleteCustomKeyStoreRequest.Builder builder = DeleteCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static DeleteImportedKeyMaterialRequest DeleteImportedKeyMaterialRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteImportedKeyMaterialRequest dafnyValue) {
    DeleteImportedKeyMaterialRequest.Builder builder = DeleteImportedKeyMaterialRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DescribeCustomKeyStoresRequest DescribeCustomKeyStoresRequest(
      Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresRequest dafnyValue) {
    DescribeCustomKeyStoresRequest.Builder builder = DescribeCustomKeyStoresRequest.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreName().is_Some()) {
      builder.customKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeKeyRequest DescribeKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.DescribeKeyRequest dafnyValue) {
    DescribeKeyRequest.Builder builder = DescribeKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static DisableKeyRequest DisableKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisableKeyRequest dafnyValue) {
    DisableKeyRequest.Builder builder = DisableKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DisableKeyRotationRequest DisableKeyRotationRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisableKeyRotationRequest dafnyValue) {
    DisableKeyRotationRequest.Builder builder = DisableKeyRotationRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DisconnectCustomKeyStoreRequest DisconnectCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreRequest dafnyValue) {
    DisconnectCustomKeyStoreRequest.Builder builder = DisconnectCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static EnableKeyRequest EnableKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.EnableKeyRequest dafnyValue) {
    EnableKeyRequest.Builder builder = EnableKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static EnableKeyRotationRequest EnableKeyRotationRequest(
      Dafny.Com.Amazonaws.Kms.Types.EnableKeyRotationRequest dafnyValue) {
    EnableKeyRotationRequest.Builder builder = EnableKeyRotationRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static EncryptRequest EncryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.EncryptRequest dafnyValue) {
    EncryptRequest.Builder builder = EncryptRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().toRawArray())));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyRequest GenerateDataKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyRequest dafnyValue) {
    GenerateDataKeyRequest.Builder builder = GenerateDataKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyPairRequest GenerateDataKeyPairRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairRequest dafnyValue) {
    GenerateDataKeyPairRequest.Builder builder = GenerateDataKeyPairRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyPairWithoutPlaintextRequest GenerateDataKeyPairWithoutPlaintextRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyPairWithoutPlaintextRequest.Builder builder = GenerateDataKeyPairWithoutPlaintextRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyWithoutPlaintextRequest GenerateDataKeyWithoutPlaintextRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyWithoutPlaintextRequest.Builder builder = GenerateDataKeyWithoutPlaintextRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateRandomRequest GenerateRandomRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateRandomRequest dafnyValue) {
    GenerateRandomRequest.Builder builder = GenerateRandomRequest.builder();
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    return builder.build();
  }

  public static GetKeyPolicyRequest GetKeyPolicyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyRequest dafnyValue) {
    GetKeyPolicyRequest.Builder builder = GetKeyPolicyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.policyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    return builder.build();
  }

  public static GetKeyRotationStatusRequest GetKeyRotationStatusRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusRequest dafnyValue) {
    GetKeyRotationStatusRequest.Builder builder = GetKeyRotationStatusRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static GetParametersForImportRequest GetParametersForImportRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportRequest dafnyValue) {
    GetParametersForImportRequest.Builder builder = GetParametersForImportRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.wrappingAlgorithm(ToNative.AlgorithmSpec(dafnyValue.dtor_WrappingAlgorithm()));
    builder.wrappingKeySpec(ToNative.WrappingKeySpec(dafnyValue.dtor_WrappingKeySpec()));
    return builder.build();
  }

  public static GetPublicKeyRequest GetPublicKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyRequest dafnyValue) {
    GetPublicKeyRequest.Builder builder = GetPublicKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static ImportKeyMaterialRequest ImportKeyMaterialRequest(
      Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialRequest dafnyValue) {
    ImportKeyMaterialRequest.Builder builder = ImportKeyMaterialRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.importToken(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ImportToken().toRawArray())));
    builder.encryptedKeyMaterial(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_EncryptedKeyMaterial().toRawArray())));
    if (dafnyValue.dtor_ValidTo().is_Some()) {
      builder.validTo(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ValidTo().dtor_value()));
    }
    if (dafnyValue.dtor_ExpirationModel().is_Some()) {
      builder.expirationModel(ToNative.ExpirationModelType(dafnyValue.dtor_ExpirationModel().dtor_value()));
    }
    return builder.build();
  }

  public static ListAliasesRequest ListAliasesRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListAliasesRequest dafnyValue) {
    ListAliasesRequest.Builder builder = ListAliasesRequest.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListGrantsRequest ListGrantsRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListGrantsRequest dafnyValue) {
    ListGrantsRequest.Builder builder = ListGrantsRequest.builder();
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_GranteePrincipal().is_Some()) {
      builder.granteePrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal().dtor_value()));
    }
    return builder.build();
  }

  public static ListKeyPoliciesRequest ListKeyPoliciesRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesRequest dafnyValue) {
    ListKeyPoliciesRequest.Builder builder = ListKeyPoliciesRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListResourceTagsRequest ListResourceTagsRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsRequest dafnyValue) {
    ListResourceTagsRequest.Builder builder = ListResourceTagsRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static PutKeyPolicyRequest PutKeyPolicyRequest(
      Dafny.Com.Amazonaws.Kms.Types.PutKeyPolicyRequest dafnyValue) {
    PutKeyPolicyRequest.Builder builder = PutKeyPolicyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.policyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    builder.policy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy()));
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    return builder.build();
  }

  public static ReEncryptRequest ReEncryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.ReEncryptRequest dafnyValue) {
    ReEncryptRequest.Builder builder = ReEncryptRequest.builder();
    builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().toRawArray())));
    if (dafnyValue.dtor_SourceEncryptionContext().is_Some()) {
      builder.sourceEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_SourceEncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_SourceKeyId().is_Some()) {
      builder.sourceKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceKeyId().dtor_value()));
    }
    builder.destinationKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_DestinationKeyId()));
    if (dafnyValue.dtor_DestinationEncryptionContext().is_Some()) {
      builder.destinationEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_DestinationEncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionAlgorithm().is_Some()) {
      builder.sourceEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_SourceEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationEncryptionAlgorithm().is_Some()) {
      builder.destinationEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_DestinationEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicateKeyRequest ReplicateKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyRequest dafnyValue) {
    ReplicateKeyRequest.Builder builder = ReplicateKeyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.replicaRegion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaRegion()));
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return builder.build();
  }

  public static RetireGrantRequest RetireGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.RetireGrantRequest dafnyValue) {
    RetireGrantRequest.Builder builder = RetireGrantRequest.builder();
    if (dafnyValue.dtor_GrantToken().is_Some()) {
      builder.grantToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantToken().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    return builder.build();
  }

  public static RevokeGrantRequest RevokeGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.RevokeGrantRequest dafnyValue) {
    RevokeGrantRequest.Builder builder = RevokeGrantRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.grantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId()));
    return builder.build();
  }

  public static ScheduleKeyDeletionRequest ScheduleKeyDeletionRequest(
      Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionRequest dafnyValue) {
    ScheduleKeyDeletionRequest.Builder builder = ScheduleKeyDeletionRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_PendingWindowInDays().is_Some()) {
      builder.pendingWindowInDays((dafnyValue.dtor_PendingWindowInDays().dtor_value()));
    }
    return builder.build();
  }

  public static SignRequest SignRequest(Dafny.Com.Amazonaws.Kms.Types.SignRequest dafnyValue) {
    SignRequest.Builder builder = SignRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.message(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Message().toRawArray())));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      builder.messageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    return builder.build();
  }

  public static TagResourceRequest TagResourceRequest(
      Dafny.Com.Amazonaws.Kms.Types.TagResourceRequest dafnyValue) {
    TagResourceRequest.Builder builder = TagResourceRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.tags(ToNative.TagList(dafnyValue.dtor_Tags()));
    return builder.build();
  }

  public static UntagResourceRequest UntagResourceRequest(
      Dafny.Com.Amazonaws.Kms.Types.UntagResourceRequest dafnyValue) {
    UntagResourceRequest.Builder builder = UntagResourceRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.tagKeys(ToNative.TagKeyList(dafnyValue.dtor_TagKeys()));
    return builder.build();
  }

  public static UpdateAliasRequest UpdateAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateAliasRequest dafnyValue) {
    UpdateAliasRequest.Builder builder = UpdateAliasRequest.builder();
    builder.aliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    builder.targetKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return builder.build();
  }

  public static UpdateCustomKeyStoreRequest UpdateCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreRequest dafnyValue) {
    UpdateCustomKeyStoreRequest.Builder builder = UpdateCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    if (dafnyValue.dtor_NewCustomKeyStoreName().is_Some()) {
      builder.newCustomKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NewCustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_KeyStorePassword().is_Some()) {
      builder.keyStorePassword(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword().dtor_value()));
    }
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateKeyDescriptionRequest UpdateKeyDescriptionRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateKeyDescriptionRequest dafnyValue) {
    UpdateKeyDescriptionRequest.Builder builder = UpdateKeyDescriptionRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.description(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description()));
    return builder.build();
  }

  public static UpdatePrimaryRegionRequest UpdatePrimaryRegionRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdatePrimaryRegionRequest dafnyValue) {
    UpdatePrimaryRegionRequest.Builder builder = UpdatePrimaryRegionRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.primaryRegion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PrimaryRegion()));
    return builder.build();
  }

  public static VerifyRequest VerifyRequest(
      Dafny.Com.Amazonaws.Kms.Types.VerifyRequest dafnyValue) {
    VerifyRequest.Builder builder = VerifyRequest.builder();
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.message(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Message().toRawArray())));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      builder.messageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    builder.signature(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Signature().toRawArray())));
    builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return builder.build();
  }

  public static CancelKeyDeletionResponse CancelKeyDeletionResponse(
      Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionResponse dafnyValue) {
    CancelKeyDeletionResponse.Builder builder = CancelKeyDeletionResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static ConnectCustomKeyStoreResponse ConnectCustomKeyStoreResponse(
      Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreResponse dafnyValue) {
    return ConnectCustomKeyStoreResponse.builder().build();
  }

  public static CreateCustomKeyStoreResponse CreateCustomKeyStoreResponse(
      Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreResponse dafnyValue) {
    CreateCustomKeyStoreResponse.Builder builder = CreateCustomKeyStoreResponse.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    return builder.build();
  }

  public static CreateGrantResponse CreateGrantResponse(
      Dafny.Com.Amazonaws.Kms.Types.CreateGrantResponse dafnyValue) {
    CreateGrantResponse.Builder builder = CreateGrantResponse.builder();
    if (dafnyValue.dtor_GrantToken().is_Some()) {
      builder.grantToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantToken().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    return builder.build();
  }

  public static CreateKeyResponse CreateKeyResponse(
      Dafny.Com.Amazonaws.Kms.Types.CreateKeyResponse dafnyValue) {
    CreateKeyResponse.Builder builder = CreateKeyResponse.builder();
    if (dafnyValue.dtor_KeyMetadata().is_Some()) {
      builder.keyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_KeyMetadata().dtor_value()));
    }
    return builder.build();
  }

  public static DecryptResponse DecryptResponse(
      Dafny.Com.Amazonaws.Kms.Types.DecryptResponse dafnyValue) {
    DecryptResponse.Builder builder = DecryptResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static DeleteCustomKeyStoreResponse DeleteCustomKeyStoreResponse(
      Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreResponse dafnyValue) {
    return DeleteCustomKeyStoreResponse.builder().build();
  }

  public static DescribeCustomKeyStoresResponse DescribeCustomKeyStoresResponse(
      Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresResponse dafnyValue) {
    DescribeCustomKeyStoresResponse.Builder builder = DescribeCustomKeyStoresResponse.builder();
    if (dafnyValue.dtor_CustomKeyStores().is_Some()) {
      builder.customKeyStores(ToNative.CustomKeyStoresList(dafnyValue.dtor_CustomKeyStores().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeKeyResponse DescribeKeyResponse(
      Dafny.Com.Amazonaws.Kms.Types.DescribeKeyResponse dafnyValue) {
    DescribeKeyResponse.Builder builder = DescribeKeyResponse.builder();
    if (dafnyValue.dtor_KeyMetadata().is_Some()) {
      builder.keyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_KeyMetadata().dtor_value()));
    }
    return builder.build();
  }

  public static DisconnectCustomKeyStoreResponse DisconnectCustomKeyStoreResponse(
      Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreResponse dafnyValue) {
    return DisconnectCustomKeyStoreResponse.builder().build();
  }

  public static EncryptResponse EncryptResponse(
      Dafny.Com.Amazonaws.Kms.Types.EncryptResponse dafnyValue) {
    EncryptResponse.Builder builder = EncryptResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyResponse GenerateDataKeyResponse(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyResponse dafnyValue) {
    GenerateDataKeyResponse.Builder builder = GenerateDataKeyResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyPairResponse GenerateDataKeyPairResponse(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairResponse dafnyValue) {
    GenerateDataKeyPairResponse.Builder builder = GenerateDataKeyPairResponse.builder();
    if (dafnyValue.dtor_PrivateKeyCiphertextBlob().is_Some()) {
      builder.privateKeyCiphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyCiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PrivateKeyPlaintext().is_Some()) {
      builder.privateKeyPlaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyPlaintext().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyPairSpec().is_Some()) {
      builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyPairWithoutPlaintextResponse GenerateDataKeyPairWithoutPlaintextResponse(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextResponse dafnyValue) {
    GenerateDataKeyPairWithoutPlaintextResponse.Builder builder = GenerateDataKeyPairWithoutPlaintextResponse.builder();
    if (dafnyValue.dtor_PrivateKeyCiphertextBlob().is_Some()) {
      builder.privateKeyCiphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyCiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyPairSpec().is_Some()) {
      builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyWithoutPlaintextResponse GenerateDataKeyWithoutPlaintextResponse(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextResponse dafnyValue) {
    GenerateDataKeyWithoutPlaintextResponse.Builder builder = GenerateDataKeyWithoutPlaintextResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateRandomResponse GenerateRandomResponse(
      Dafny.Com.Amazonaws.Kms.Types.GenerateRandomResponse dafnyValue) {
    GenerateRandomResponse.Builder builder = GenerateRandomResponse.builder();
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GetKeyPolicyResponse GetKeyPolicyResponse(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyResponse dafnyValue) {
    GetKeyPolicyResponse.Builder builder = GetKeyPolicyResponse.builder();
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    return builder.build();
  }

  public static GetKeyRotationStatusResponse GetKeyRotationStatusResponse(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusResponse dafnyValue) {
    GetKeyRotationStatusResponse.Builder builder = GetKeyRotationStatusResponse.builder();
    if (dafnyValue.dtor_KeyRotationEnabled().is_Some()) {
      builder.keyRotationEnabled((dafnyValue.dtor_KeyRotationEnabled().dtor_value()));
    }
    return builder.build();
  }

  public static GetParametersForImportResponse GetParametersForImportResponse(
      Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportResponse dafnyValue) {
    GetParametersForImportResponse.Builder builder = GetParametersForImportResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ImportToken().is_Some()) {
      builder.importToken(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ImportToken().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_ParametersValidTo().is_Some()) {
      builder.parametersValidTo(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ParametersValidTo().dtor_value()));
    }
    return builder.build();
  }

  public static GetPublicKeyResponse GetPublicKeyResponse(
      Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyResponse dafnyValue) {
    GetPublicKeyResponse.Builder builder = GetPublicKeyResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithms().is_Some()) {
      builder.encryptionAlgorithms(ToNative.EncryptionAlgorithmSpecList(dafnyValue.dtor_EncryptionAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_SigningAlgorithms().is_Some()) {
      builder.signingAlgorithms(ToNative.SigningAlgorithmSpecList(dafnyValue.dtor_SigningAlgorithms().dtor_value()));
    }
    return builder.build();
  }

  public static ImportKeyMaterialResponse ImportKeyMaterialResponse(
      Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialResponse dafnyValue) {
    return ImportKeyMaterialResponse.builder().build();
  }

  public static ListAliasesResponse ListAliasesResponse(
      Dafny.Com.Amazonaws.Kms.Types.ListAliasesResponse dafnyValue) {
    ListAliasesResponse.Builder builder = ListAliasesResponse.builder();
    if (dafnyValue.dtor_Aliases().is_Some()) {
      builder.aliases(ToNative.AliasList(dafnyValue.dtor_Aliases().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListGrantsResponse ListGrantsResponse(
      Dafny.Com.Amazonaws.Kms.Types.ListGrantsResponse dafnyValue) {
    ListGrantsResponse.Builder builder = ListGrantsResponse.builder();
    if (dafnyValue.dtor_Grants().is_Some()) {
      builder.grants(ToNative.GrantList(dafnyValue.dtor_Grants().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListKeyPoliciesResponse ListKeyPoliciesResponse(
      Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesResponse dafnyValue) {
    ListKeyPoliciesResponse.Builder builder = ListKeyPoliciesResponse.builder();
    if (dafnyValue.dtor_PolicyNames().is_Some()) {
      builder.policyNames(ToNative.PolicyNameList(dafnyValue.dtor_PolicyNames().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListResourceTagsResponse ListResourceTagsResponse(
      Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsResponse dafnyValue) {
    ListResourceTagsResponse.Builder builder = ListResourceTagsResponse.builder();
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ReEncryptResponse ReEncryptResponse(
      Dafny.Com.Amazonaws.Kms.Types.ReEncryptResponse dafnyValue) {
    ReEncryptResponse.Builder builder = ReEncryptResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_SourceKeyId().is_Some()) {
      builder.sourceKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionAlgorithm().is_Some()) {
      builder.sourceEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_SourceEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationEncryptionAlgorithm().is_Some()) {
      builder.destinationEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_DestinationEncryptionAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicateKeyResponse ReplicateKeyResponse(
      Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyResponse dafnyValue) {
    ReplicateKeyResponse.Builder builder = ReplicateKeyResponse.builder();
    if (dafnyValue.dtor_ReplicaKeyMetadata().is_Some()) {
      builder.replicaKeyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_ReplicaKeyMetadata().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaPolicy().is_Some()) {
      builder.replicaPolicy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaPolicy().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTags().is_Some()) {
      builder.replicaTags(ToNative.TagList(dafnyValue.dtor_ReplicaTags().dtor_value()));
    }
    return builder.build();
  }

  public static ScheduleKeyDeletionResponse ScheduleKeyDeletionResponse(
      Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionResponse dafnyValue) {
    ScheduleKeyDeletionResponse.Builder builder = ScheduleKeyDeletionResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_DeletionDate().is_Some()) {
      builder.deletionDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_DeletionDate().dtor_value()));
    }
    if (dafnyValue.dtor_KeyState().is_Some()) {
      builder.keyState(ToNative.KeyState(dafnyValue.dtor_KeyState().dtor_value()));
    }
    if (dafnyValue.dtor_PendingWindowInDays().is_Some()) {
      builder.pendingWindowInDays((dafnyValue.dtor_PendingWindowInDays().dtor_value()));
    }
    return builder.build();
  }

  public static SignResponse SignResponse(Dafny.Com.Amazonaws.Kms.Types.SignResponse dafnyValue) {
    SignResponse.Builder builder = SignResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Signature().is_Some()) {
      builder.signature(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Signature().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_SigningAlgorithm().is_Some()) {
      builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateCustomKeyStoreResponse UpdateCustomKeyStoreResponse(
      Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreResponse dafnyValue) {
    return UpdateCustomKeyStoreResponse.builder().build();
  }

  public static VerifyResponse VerifyResponse(
      Dafny.Com.Amazonaws.Kms.Types.VerifyResponse dafnyValue) {
    VerifyResponse.Builder builder = VerifyResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_SignatureValid().is_Some()) {
      builder.signatureValid((dafnyValue.dtor_SignatureValid().dtor_value()));
    }
    if (dafnyValue.dtor_SigningAlgorithm().is_Some()) {
      builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static List<GrantOperation> GrantOperationList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.GrantOperation> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::GrantOperation);
  }

  public static GrantConstraints GrantConstraints(
      Dafny.Com.Amazonaws.Kms.Types.GrantConstraints dafnyValue) {
    GrantConstraints.Builder builder = GrantConstraints.builder();
    if (dafnyValue.dtor_EncryptionContextSubset().is_Some()) {
      builder.encryptionContextSubset(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextSubset().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionContextEquals().is_Some()) {
      builder.encryptionContextEquals(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextEquals().dtor_value()));
    }
    return builder.build();
  }

  public static List<String> GrantTokenList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static KeyUsageType KeyUsageType(Dafny.Com.Amazonaws.Kms.Types.KeyUsageType dafnyValue) {
    if (dafnyValue.is_SIGN__VERIFY()) {
      return KeyUsageType.SIGN_VERIFY;
    }
    if (dafnyValue.is_ENCRYPT__DECRYPT()) {
      return KeyUsageType.ENCRYPT_DECRYPT;
    }
    return KeyUsageType.fromValue(dafnyValue.toString());
  }

  public static CustomerMasterKeySpec CustomerMasterKeySpec(
      Dafny.Com.Amazonaws.Kms.Types.CustomerMasterKeySpec dafnyValue) {
    if (dafnyValue.is_RSA__2048()) {
      return CustomerMasterKeySpec.RSA_2048;
    }
    if (dafnyValue.is_RSA__3072()) {
      return CustomerMasterKeySpec.RSA_3072;
    }
    if (dafnyValue.is_RSA__4096()) {
      return CustomerMasterKeySpec.RSA_4096;
    }
    if (dafnyValue.is_ECC__NIST__P256()) {
      return CustomerMasterKeySpec.ECC_NIST_P256;
    }
    if (dafnyValue.is_ECC__NIST__P384()) {
      return CustomerMasterKeySpec.ECC_NIST_P384;
    }
    if (dafnyValue.is_ECC__NIST__P521()) {
      return CustomerMasterKeySpec.ECC_NIST_P521;
    }
    if (dafnyValue.is_ECC__SECG__P256K1()) {
      return CustomerMasterKeySpec.ECC_SECG_P256_K1;
    }
    if (dafnyValue.is_SYMMETRIC__DEFAULT()) {
      return CustomerMasterKeySpec.SYMMETRIC_DEFAULT;
    }
    return CustomerMasterKeySpec.fromValue(dafnyValue.toString());
  }

  public static KeySpec KeySpec(Dafny.Com.Amazonaws.Kms.Types.KeySpec dafnyValue) {
    if (dafnyValue.is_RSA__2048()) {
      return KeySpec.RSA_2048;
    }
    if (dafnyValue.is_RSA__3072()) {
      return KeySpec.RSA_3072;
    }
    if (dafnyValue.is_RSA__4096()) {
      return KeySpec.RSA_4096;
    }
    if (dafnyValue.is_ECC__NIST__P256()) {
      return KeySpec.ECC_NIST_P256;
    }
    if (dafnyValue.is_ECC__NIST__P384()) {
      return KeySpec.ECC_NIST_P384;
    }
    if (dafnyValue.is_ECC__NIST__P521()) {
      return KeySpec.ECC_NIST_P521;
    }
    if (dafnyValue.is_ECC__SECG__P256K1()) {
      return KeySpec.ECC_SECG_P256_K1;
    }
    if (dafnyValue.is_SYMMETRIC__DEFAULT()) {
      return KeySpec.SYMMETRIC_DEFAULT;
    }
    return KeySpec.fromValue(dafnyValue.toString());
  }

  public static OriginType OriginType(Dafny.Com.Amazonaws.Kms.Types.OriginType dafnyValue) {
    if (dafnyValue.is_AWS__KMS()) {
      return OriginType.AWS_KMS;
    }
    if (dafnyValue.is_EXTERNAL()) {
      return OriginType.EXTERNAL;
    }
    if (dafnyValue.is_AWS__CLOUDHSM()) {
      return OriginType.AWS_CLOUDHSM;
    }
    return OriginType.fromValue(dafnyValue.toString());
  }

  public static List<Tag> TagList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.Tag> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::Tag);
  }

  public static Map<String, String> EncryptionContextType(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static EncryptionAlgorithmSpec EncryptionAlgorithmSpec(
      Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec dafnyValue) {
    if (dafnyValue.is_SYMMETRIC__DEFAULT()) {
      return EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT;
    }
    if (dafnyValue.is_RSAES__OAEP__SHA__1()) {
      return EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1;
    }
    if (dafnyValue.is_RSAES__OAEP__SHA__256()) {
      return EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256;
    }
    return EncryptionAlgorithmSpec.fromValue(dafnyValue.toString());
  }

  public static DataKeySpec DataKeySpec(Dafny.Com.Amazonaws.Kms.Types.DataKeySpec dafnyValue) {
    if (dafnyValue.is_AES__256()) {
      return DataKeySpec.AES_256;
    }
    if (dafnyValue.is_AES__128()) {
      return DataKeySpec.AES_128;
    }
    return DataKeySpec.fromValue(dafnyValue.toString());
  }

  public static DataKeyPairSpec DataKeyPairSpec(
      Dafny.Com.Amazonaws.Kms.Types.DataKeyPairSpec dafnyValue) {
    if (dafnyValue.is_RSA__2048()) {
      return DataKeyPairSpec.RSA_2048;
    }
    if (dafnyValue.is_RSA__3072()) {
      return DataKeyPairSpec.RSA_3072;
    }
    if (dafnyValue.is_RSA__4096()) {
      return DataKeyPairSpec.RSA_4096;
    }
    if (dafnyValue.is_ECC__NIST__P256()) {
      return DataKeyPairSpec.ECC_NIST_P256;
    }
    if (dafnyValue.is_ECC__NIST__P384()) {
      return DataKeyPairSpec.ECC_NIST_P384;
    }
    if (dafnyValue.is_ECC__NIST__P521()) {
      return DataKeyPairSpec.ECC_NIST_P521;
    }
    if (dafnyValue.is_ECC__SECG__P256K1()) {
      return DataKeyPairSpec.ECC_SECG_P256_K1;
    }
    return DataKeyPairSpec.fromValue(dafnyValue.toString());
  }

  public static AlgorithmSpec AlgorithmSpec(
      Dafny.Com.Amazonaws.Kms.Types.AlgorithmSpec dafnyValue) {
    if (dafnyValue.is_RSAES__PKCS1__V1__5()) {
      return AlgorithmSpec.RSAES_PKCS1_V1_5;
    }
    if (dafnyValue.is_RSAES__OAEP__SHA__1()) {
      return AlgorithmSpec.RSAES_OAEP_SHA_1;
    }
    if (dafnyValue.is_RSAES__OAEP__SHA__256()) {
      return AlgorithmSpec.RSAES_OAEP_SHA_256;
    }
    return AlgorithmSpec.fromValue(dafnyValue.toString());
  }

  public static WrappingKeySpec WrappingKeySpec(
      Dafny.Com.Amazonaws.Kms.Types.WrappingKeySpec dafnyValue) {
    if (dafnyValue.is_RSA__2048()) {
      return WrappingKeySpec.RSA_2048;
    }
    return WrappingKeySpec.fromValue(dafnyValue.toString());
  }

  public static ExpirationModelType ExpirationModelType(
      Dafny.Com.Amazonaws.Kms.Types.ExpirationModelType dafnyValue) {
    if (dafnyValue.is_KEY__MATERIAL__EXPIRES()) {
      return ExpirationModelType.KEY_MATERIAL_EXPIRES;
    }
    if (dafnyValue.is_KEY__MATERIAL__DOES__NOT__EXPIRE()) {
      return ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE;
    }
    return ExpirationModelType.fromValue(dafnyValue.toString());
  }

  public static MessageType MessageType(Dafny.Com.Amazonaws.Kms.Types.MessageType dafnyValue) {
    if (dafnyValue.is_RAW()) {
      return MessageType.RAW;
    }
    if (dafnyValue.is_DIGEST()) {
      return MessageType.DIGEST;
    }
    return MessageType.fromValue(dafnyValue.toString());
  }

  public static SigningAlgorithmSpec SigningAlgorithmSpec(
      Dafny.Com.Amazonaws.Kms.Types.SigningAlgorithmSpec dafnyValue) {
    if (dafnyValue.is_RSASSA__PSS__SHA__256()) {
      return SigningAlgorithmSpec.RSASSA_PSS_SHA_256;
    }
    if (dafnyValue.is_RSASSA__PSS__SHA__384()) {
      return SigningAlgorithmSpec.RSASSA_PSS_SHA_384;
    }
    if (dafnyValue.is_RSASSA__PSS__SHA__512()) {
      return SigningAlgorithmSpec.RSASSA_PSS_SHA_512;
    }
    if (dafnyValue.is_RSASSA__PKCS1__V1__5__SHA__256()) {
      return SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256;
    }
    if (dafnyValue.is_RSASSA__PKCS1__V1__5__SHA__384()) {
      return SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384;
    }
    if (dafnyValue.is_RSASSA__PKCS1__V1__5__SHA__512()) {
      return SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512;
    }
    if (dafnyValue.is_ECDSA__SHA__256()) {
      return SigningAlgorithmSpec.ECDSA_SHA_256;
    }
    if (dafnyValue.is_ECDSA__SHA__384()) {
      return SigningAlgorithmSpec.ECDSA_SHA_384;
    }
    if (dafnyValue.is_ECDSA__SHA__512()) {
      return SigningAlgorithmSpec.ECDSA_SHA_512;
    }
    return SigningAlgorithmSpec.fromValue(dafnyValue.toString());
  }

  public static List<String> TagKeyList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static KeyMetadata KeyMetadata(Dafny.Com.Amazonaws.Kms.Types.KeyMetadata dafnyValue) {
    KeyMetadata.Builder builder = KeyMetadata.builder();
    if (dafnyValue.dtor_AWSAccountId().is_Some()) {
      builder.awsAccountId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AWSAccountId().dtor_value()));
    }
    builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Arn().is_Some()) {
      builder.arn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Arn().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_Enabled().is_Some()) {
      builder.enabled((dafnyValue.dtor_Enabled().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_KeyState().is_Some()) {
      builder.keyState(ToNative.KeyState(dafnyValue.dtor_KeyState().dtor_value()));
    }
    if (dafnyValue.dtor_DeletionDate().is_Some()) {
      builder.deletionDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_DeletionDate().dtor_value()));
    }
    if (dafnyValue.dtor_ValidTo().is_Some()) {
      builder.validTo(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ValidTo().dtor_value()));
    }
    if (dafnyValue.dtor_Origin().is_Some()) {
      builder.origin(ToNative.OriginType(dafnyValue.dtor_Origin().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    if (dafnyValue.dtor_ExpirationModel().is_Some()) {
      builder.expirationModel(ToNative.ExpirationModelType(dafnyValue.dtor_ExpirationModel().dtor_value()));
    }
    if (dafnyValue.dtor_KeyManager().is_Some()) {
      builder.keyManager(ToNative.KeyManagerType(dafnyValue.dtor_KeyManager().dtor_value()));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithms().is_Some()) {
      builder.encryptionAlgorithms(ToNative.EncryptionAlgorithmSpecList(dafnyValue.dtor_EncryptionAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_SigningAlgorithms().is_Some()) {
      builder.signingAlgorithms(ToNative.SigningAlgorithmSpecList(dafnyValue.dtor_SigningAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegion().is_Some()) {
      builder.multiRegion((dafnyValue.dtor_MultiRegion().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegionConfiguration().is_Some()) {
      builder.multiRegionConfiguration(ToNative.MultiRegionConfiguration(dafnyValue.dtor_MultiRegionConfiguration().dtor_value()));
    }
    if (dafnyValue.dtor_PendingDeletionWindowInDays().is_Some()) {
      builder.pendingDeletionWindowInDays((dafnyValue.dtor_PendingDeletionWindowInDays().dtor_value()));
    }
    return builder.build();
  }

  public static List<CustomKeyStoresListEntry> CustomKeyStoresList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.CustomKeyStoresListEntry> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::CustomKeyStoresListEntry);
  }

  public static List<EncryptionAlgorithmSpec> EncryptionAlgorithmSpecList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::EncryptionAlgorithmSpec);
  }

  public static List<SigningAlgorithmSpec> SigningAlgorithmSpecList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.SigningAlgorithmSpec> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::SigningAlgorithmSpec);
  }

  public static List<AliasListEntry> AliasList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.AliasListEntry> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::AliasListEntry);
  }

  public static List<GrantListEntry> GrantList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.GrantListEntry> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::GrantListEntry);
  }

  public static List<String> PolicyNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static KeyState KeyState(Dafny.Com.Amazonaws.Kms.Types.KeyState dafnyValue) {
    if (dafnyValue.is_Creating()) {
      return KeyState.CREATING;
    }
    if (dafnyValue.is_Enabled()) {
      return KeyState.ENABLED;
    }
    if (dafnyValue.is_Disabled()) {
      return KeyState.DISABLED;
    }
    if (dafnyValue.is_PendingDeletion()) {
      return KeyState.PENDING_DELETION;
    }
    if (dafnyValue.is_PendingImport()) {
      return KeyState.PENDING_IMPORT;
    }
    if (dafnyValue.is_PendingReplicaDeletion()) {
      return KeyState.PENDING_REPLICA_DELETION;
    }
    if (dafnyValue.is_Unavailable()) {
      return KeyState.UNAVAILABLE;
    }
    if (dafnyValue.is_Updating()) {
      return KeyState.UPDATING;
    }
    return KeyState.fromValue(dafnyValue.toString());
  }

  public static GrantOperation GrantOperation(
      Dafny.Com.Amazonaws.Kms.Types.GrantOperation dafnyValue) {
    if (dafnyValue.is_Decrypt()) {
      return GrantOperation.DECRYPT;
    }
    if (dafnyValue.is_Encrypt()) {
      return GrantOperation.ENCRYPT;
    }
    if (dafnyValue.is_GenerateDataKey()) {
      return GrantOperation.GENERATE_DATA_KEY;
    }
    if (dafnyValue.is_GenerateDataKeyWithoutPlaintext()) {
      return GrantOperation.GENERATE_DATA_KEY_WITHOUT_PLAINTEXT;
    }
    if (dafnyValue.is_ReEncryptFrom()) {
      return GrantOperation.RE_ENCRYPT_FROM;
    }
    if (dafnyValue.is_ReEncryptTo()) {
      return GrantOperation.RE_ENCRYPT_TO;
    }
    if (dafnyValue.is_Sign()) {
      return GrantOperation.SIGN;
    }
    if (dafnyValue.is_Verify()) {
      return GrantOperation.VERIFY;
    }
    if (dafnyValue.is_GetPublicKey()) {
      return GrantOperation.GET_PUBLIC_KEY;
    }
    if (dafnyValue.is_CreateGrant()) {
      return GrantOperation.CREATE_GRANT;
    }
    if (dafnyValue.is_RetireGrant()) {
      return GrantOperation.RETIRE_GRANT;
    }
    if (dafnyValue.is_DescribeKey()) {
      return GrantOperation.DESCRIBE_KEY;
    }
    if (dafnyValue.is_GenerateDataKeyPair()) {
      return GrantOperation.GENERATE_DATA_KEY_PAIR;
    }
    if (dafnyValue.is_GenerateDataKeyPairWithoutPlaintext()) {
      return GrantOperation.GENERATE_DATA_KEY_PAIR_WITHOUT_PLAINTEXT;
    }
    return GrantOperation.fromValue(dafnyValue.toString());
  }

  public static Tag Tag(Dafny.Com.Amazonaws.Kms.Types.Tag dafnyValue) {
    Tag.Builder builder = Tag.builder();
    builder.tagKey(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagKey()));
    builder.tagValue(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagValue()));
    return builder.build();
  }

  public static KeyManagerType KeyManagerType(
      Dafny.Com.Amazonaws.Kms.Types.KeyManagerType dafnyValue) {
    if (dafnyValue.is_AWS()) {
      return KeyManagerType.AWS;
    }
    if (dafnyValue.is_CUSTOMER()) {
      return KeyManagerType.CUSTOMER;
    }
    return KeyManagerType.fromValue(dafnyValue.toString());
  }

  public static MultiRegionConfiguration MultiRegionConfiguration(
      Dafny.Com.Amazonaws.Kms.Types.MultiRegionConfiguration dafnyValue) {
    MultiRegionConfiguration.Builder builder = MultiRegionConfiguration.builder();
    if (dafnyValue.dtor_MultiRegionKeyType().is_Some()) {
      builder.multiRegionKeyType(ToNative.MultiRegionKeyType(dafnyValue.dtor_MultiRegionKeyType().dtor_value()));
    }
    if (dafnyValue.dtor_PrimaryKey().is_Some()) {
      builder.primaryKey(ToNative.MultiRegionKey(dafnyValue.dtor_PrimaryKey().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaKeys().is_Some()) {
      builder.replicaKeys(ToNative.MultiRegionKeyList(dafnyValue.dtor_ReplicaKeys().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoresListEntry CustomKeyStoresListEntry(
      Dafny.Com.Amazonaws.Kms.Types.CustomKeyStoresListEntry dafnyValue) {
    CustomKeyStoresListEntry.Builder builder = CustomKeyStoresListEntry.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreName().is_Some()) {
      builder.customKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    if (dafnyValue.dtor_TrustAnchorCertificate().is_Some()) {
      builder.trustAnchorCertificate(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TrustAnchorCertificate().dtor_value()));
    }
    if (dafnyValue.dtor_ConnectionState().is_Some()) {
      builder.connectionState(ToNative.ConnectionStateType(dafnyValue.dtor_ConnectionState().dtor_value()));
    }
    if (dafnyValue.dtor_ConnectionErrorCode().is_Some()) {
      builder.connectionErrorCode(ToNative.ConnectionErrorCodeType(dafnyValue.dtor_ConnectionErrorCode().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    return builder.build();
  }

  public static AliasListEntry AliasListEntry(
      Dafny.Com.Amazonaws.Kms.Types.AliasListEntry dafnyValue) {
    AliasListEntry.Builder builder = AliasListEntry.builder();
    if (dafnyValue.dtor_AliasName().is_Some()) {
      builder.aliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName().dtor_value()));
    }
    if (dafnyValue.dtor_AliasArn().is_Some()) {
      builder.aliasArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasArn().dtor_value()));
    }
    if (dafnyValue.dtor_TargetKeyId().is_Some()) {
      builder.targetKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdatedDate().is_Some()) {
      builder.lastUpdatedDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastUpdatedDate().dtor_value()));
    }
    return builder.build();
  }

  public static GrantListEntry GrantListEntry(
      Dafny.Com.Amazonaws.Kms.Types.GrantListEntry dafnyValue) {
    GrantListEntry.Builder builder = GrantListEntry.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_Name().is_Some()) {
      builder.name(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Name().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_GranteePrincipal().is_Some()) {
      builder.granteePrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal().dtor_value()));
    }
    if (dafnyValue.dtor_RetiringPrincipal().is_Some()) {
      builder.retiringPrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RetiringPrincipal().dtor_value()));
    }
    if (dafnyValue.dtor_IssuingAccount().is_Some()) {
      builder.issuingAccount(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IssuingAccount().dtor_value()));
    }
    if (dafnyValue.dtor_Operations().is_Some()) {
      builder.operations(ToNative.GrantOperationList(dafnyValue.dtor_Operations().dtor_value()));
    }
    if (dafnyValue.dtor_Constraints().is_Some()) {
      builder.constraints(ToNative.GrantConstraints(dafnyValue.dtor_Constraints().dtor_value()));
    }
    return builder.build();
  }

  public static MultiRegionKeyType MultiRegionKeyType(
      Dafny.Com.Amazonaws.Kms.Types.MultiRegionKeyType dafnyValue) {
    if (dafnyValue.is_PRIMARY()) {
      return MultiRegionKeyType.PRIMARY;
    }
    if (dafnyValue.is_REPLICA()) {
      return MultiRegionKeyType.REPLICA;
    }
    return MultiRegionKeyType.fromValue(dafnyValue.toString());
  }

  public static MultiRegionKey MultiRegionKey(
      Dafny.Com.Amazonaws.Kms.Types.MultiRegionKey dafnyValue) {
    MultiRegionKey.Builder builder = MultiRegionKey.builder();
    if (dafnyValue.dtor_Arn().is_Some()) {
      builder.arn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Arn().dtor_value()));
    }
    if (dafnyValue.dtor_Region().is_Some()) {
      builder.region(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Region().dtor_value()));
    }
    return builder.build();
  }

  public static List<MultiRegionKey> MultiRegionKeyList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.MultiRegionKey> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::MultiRegionKey);
  }

  public static ConnectionStateType ConnectionStateType(
      Dafny.Com.Amazonaws.Kms.Types.ConnectionStateType dafnyValue) {
    if (dafnyValue.is_CONNECTED()) {
      return ConnectionStateType.CONNECTED;
    }
    if (dafnyValue.is_CONNECTING()) {
      return ConnectionStateType.CONNECTING;
    }
    if (dafnyValue.is_FAILED()) {
      return ConnectionStateType.FAILED;
    }
    if (dafnyValue.is_DISCONNECTED()) {
      return ConnectionStateType.DISCONNECTED;
    }
    if (dafnyValue.is_DISCONNECTING()) {
      return ConnectionStateType.DISCONNECTING;
    }
    return ConnectionStateType.fromValue(dafnyValue.toString());
  }

  public static ConnectionErrorCodeType ConnectionErrorCodeType(
      Dafny.Com.Amazonaws.Kms.Types.ConnectionErrorCodeType dafnyValue) {
    if (dafnyValue.is_INVALID__CREDENTIALS()) {
      return ConnectionErrorCodeType.INVALID_CREDENTIALS;
    }
    if (dafnyValue.is_CLUSTER__NOT__FOUND()) {
      return ConnectionErrorCodeType.CLUSTER_NOT_FOUND;
    }
    if (dafnyValue.is_NETWORK__ERRORS()) {
      return ConnectionErrorCodeType.NETWORK_ERRORS;
    }
    if (dafnyValue.is_INTERNAL__ERROR()) {
      return ConnectionErrorCodeType.INTERNAL_ERROR;
    }
    if (dafnyValue.is_INSUFFICIENT__CLOUDHSM__HSMS()) {
      return ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS;
    }
    if (dafnyValue.is_USER__LOCKED__OUT()) {
      return ConnectionErrorCodeType.USER_LOCKED_OUT;
    }
    if (dafnyValue.is_USER__NOT__FOUND()) {
      return ConnectionErrorCodeType.USER_NOT_FOUND;
    }
    if (dafnyValue.is_USER__LOGGED__IN()) {
      return ConnectionErrorCodeType.USER_LOGGED_IN;
    }
    if (dafnyValue.is_SUBNET__NOT__FOUND()) {
      return ConnectionErrorCodeType.SUBNET_NOT_FOUND;
    }
    return ConnectionErrorCodeType.fromValue(dafnyValue.toString());
  }

  public static AlreadyExistsException Error(Error_AlreadyExistsException dafnyValue) {
    AlreadyExistsException.Builder builder = AlreadyExistsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterInUseException Error(
      Error_CloudHsmClusterInUseException dafnyValue) {
    CloudHsmClusterInUseException.Builder builder = CloudHsmClusterInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterInvalidConfigurationException Error(
      Error_CloudHsmClusterInvalidConfigurationException dafnyValue) {
    CloudHsmClusterInvalidConfigurationException.Builder builder = CloudHsmClusterInvalidConfigurationException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotActiveException Error(
      Error_CloudHsmClusterNotActiveException dafnyValue) {
    CloudHsmClusterNotActiveException.Builder builder = CloudHsmClusterNotActiveException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotFoundException Error(
      Error_CloudHsmClusterNotFoundException dafnyValue) {
    CloudHsmClusterNotFoundException.Builder builder = CloudHsmClusterNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotRelatedException Error(
      Error_CloudHsmClusterNotRelatedException dafnyValue) {
    CloudHsmClusterNotRelatedException.Builder builder = CloudHsmClusterNotRelatedException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreHasCmKsException Error(
      Error_CustomKeyStoreHasCMKsException dafnyValue) {
    CustomKeyStoreHasCmKsException.Builder builder = CustomKeyStoreHasCmKsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreInvalidStateException Error(
      Error_CustomKeyStoreInvalidStateException dafnyValue) {
    CustomKeyStoreInvalidStateException.Builder builder = CustomKeyStoreInvalidStateException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreNameInUseException Error(
      Error_CustomKeyStoreNameInUseException dafnyValue) {
    CustomKeyStoreNameInUseException.Builder builder = CustomKeyStoreNameInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreNotFoundException Error(
      Error_CustomKeyStoreNotFoundException dafnyValue) {
    CustomKeyStoreNotFoundException.Builder builder = CustomKeyStoreNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static DependencyTimeoutException Error(Error_DependencyTimeoutException dafnyValue) {
    DependencyTimeoutException.Builder builder = DependencyTimeoutException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static DisabledException Error(Error_DisabledException dafnyValue) {
    DisabledException.Builder builder = DisabledException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ExpiredImportTokenException Error(Error_ExpiredImportTokenException dafnyValue) {
    ExpiredImportTokenException.Builder builder = ExpiredImportTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectKeyException Error(Error_IncorrectKeyException dafnyValue) {
    IncorrectKeyException.Builder builder = IncorrectKeyException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectKeyMaterialException Error(
      Error_IncorrectKeyMaterialException dafnyValue) {
    IncorrectKeyMaterialException.Builder builder = IncorrectKeyMaterialException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectTrustAnchorException Error(
      Error_IncorrectTrustAnchorException dafnyValue) {
    IncorrectTrustAnchorException.Builder builder = IncorrectTrustAnchorException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidAliasNameException Error(Error_InvalidAliasNameException dafnyValue) {
    InvalidAliasNameException.Builder builder = InvalidAliasNameException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidArnException Error(Error_InvalidArnException dafnyValue) {
    InvalidArnException.Builder builder = InvalidArnException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidCiphertextException Error(Error_InvalidCiphertextException dafnyValue) {
    InvalidCiphertextException.Builder builder = InvalidCiphertextException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidGrantIdException Error(Error_InvalidGrantIdException dafnyValue) {
    InvalidGrantIdException.Builder builder = InvalidGrantIdException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidGrantTokenException Error(Error_InvalidGrantTokenException dafnyValue) {
    InvalidGrantTokenException.Builder builder = InvalidGrantTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidImportTokenException Error(Error_InvalidImportTokenException dafnyValue) {
    InvalidImportTokenException.Builder builder = InvalidImportTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidKeyUsageException Error(Error_InvalidKeyUsageException dafnyValue) {
    InvalidKeyUsageException.Builder builder = InvalidKeyUsageException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidMarkerException Error(Error_InvalidMarkerException dafnyValue) {
    InvalidMarkerException.Builder builder = InvalidMarkerException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KeyUnavailableException Error(Error_KeyUnavailableException dafnyValue) {
    KeyUnavailableException.Builder builder = KeyUnavailableException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInternalException Error(Error_KMSInternalException dafnyValue) {
    KmsInternalException.Builder builder = KmsInternalException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInvalidSignatureException Error(Error_KMSInvalidSignatureException dafnyValue) {
    KmsInvalidSignatureException.Builder builder = KmsInvalidSignatureException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInvalidStateException Error(Error_KMSInvalidStateException dafnyValue) {
    KmsInvalidStateException.Builder builder = KmsInvalidStateException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static LimitExceededException Error(Error_LimitExceededException dafnyValue) {
    LimitExceededException.Builder builder = LimitExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static MalformedPolicyDocumentException Error(
      Error_MalformedPolicyDocumentException dafnyValue) {
    MalformedPolicyDocumentException.Builder builder = MalformedPolicyDocumentException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static NotFoundException Error(Error_NotFoundException dafnyValue) {
    NotFoundException.Builder builder = NotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TagException Error(Error_TagException dafnyValue) {
    TagException.Builder builder = TagException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static UnsupportedOperationException Error(
      Error_UnsupportedOperationException dafnyValue) {
    UnsupportedOperationException.Builder builder = UnsupportedOperationException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsClient KeyManagementService(IKeyManagementServiceClient dafnyValue) {
    return ((Shim) dafnyValue).impl();
  }
}
