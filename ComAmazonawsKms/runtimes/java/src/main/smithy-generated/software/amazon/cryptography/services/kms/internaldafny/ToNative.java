// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.kms.internaldafny;

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
// BEGIN MANUAL EDIT
import software.amazon.awssdk.services.kms.model.KmsException;
// END MANUAL EDIT
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
import software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException;
import software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException;
// BEGIN MANUAL EDIT
import software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque;
// END MANUAL EDIT
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;

public class ToNative {
  // BEGIN MANUAL EDIT
  public static RuntimeException Error(Error_Opaque dafnyValue) {
    if (dafnyValue.dtor_obj() instanceof KmsException) {
      return (KmsException) dafnyValue.dtor_obj();
    }
    // Because we only ever put `KmsException` into `Error_Opaque`,
    // recieving any other type here indicates a bug with the codegen.
    // Bubble up some error to indicate this failure state.
    return new IllegalStateException("Unknown error recieved from KMS.");
  }
  // END MANUAL EDIT

  public static AlgorithmSpec AlgorithmSpec(
      software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec dafnyValue) {
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

  public static List<AliasListEntry> AliasList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::AliasListEntry);
  }

  public static AliasListEntry AliasListEntry(
      software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry dafnyValue) {
    AliasListEntry.Builder builder = AliasListEntry.builder();
    if (dafnyValue.dtor_AliasArn().is_Some()) {
      builder.aliasArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasArn().dtor_value()));
    }
    if (dafnyValue.dtor_AliasName().is_Some()) {
      builder.aliasName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdatedDate().is_Some()) {
      builder.lastUpdatedDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastUpdatedDate().dtor_value()));
    }
    if (dafnyValue.dtor_TargetKeyId().is_Some()) {
      builder.targetKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId().dtor_value()));
    }
    return builder.build();
  }

  public static CancelKeyDeletionRequest CancelKeyDeletionRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest dafnyValue) {
    CancelKeyDeletionRequest.Builder builder = CancelKeyDeletionRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static CancelKeyDeletionResponse CancelKeyDeletionResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse dafnyValue) {
    CancelKeyDeletionResponse.Builder builder = CancelKeyDeletionResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static ConnectCustomKeyStoreRequest ConnectCustomKeyStoreRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest dafnyValue) {
    ConnectCustomKeyStoreRequest.Builder builder = ConnectCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static ConnectCustomKeyStoreResponse ConnectCustomKeyStoreResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse dafnyValue) {
    return ConnectCustomKeyStoreResponse.builder().build();
  }

  public static ConnectionErrorCodeType ConnectionErrorCodeType(
      software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType dafnyValue) {
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

  public static ConnectionStateType ConnectionStateType(
      software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType dafnyValue) {
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

  public static CreateAliasRequest CreateAliasRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest dafnyValue) {
    CreateAliasRequest.Builder builder = CreateAliasRequest.builder();
    builder.aliasName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    builder.targetKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return builder.build();
  }

  public static CreateCustomKeyStoreRequest CreateCustomKeyStoreRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest dafnyValue) {
    CreateCustomKeyStoreRequest.Builder builder = CreateCustomKeyStoreRequest.builder();
    builder.cloudHsmClusterId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId()));
    builder.customKeyStoreName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName()));
    builder.keyStorePassword(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword()));
    builder.trustAnchorCertificate(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TrustAnchorCertificate()));
    return builder.build();
  }

  public static CreateCustomKeyStoreResponse CreateCustomKeyStoreResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse dafnyValue) {
    CreateCustomKeyStoreResponse.Builder builder = CreateCustomKeyStoreResponse.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    return builder.build();
  }

  public static CreateGrantRequest CreateGrantRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest dafnyValue) {
    CreateGrantRequest.Builder builder = CreateGrantRequest.builder();
    if (dafnyValue.dtor_Constraints().is_Some()) {
      builder.constraints(ToNative.GrantConstraints(dafnyValue.dtor_Constraints().dtor_value()));
    }
    builder.granteePrincipal(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Name().is_Some()) {
      builder.name(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Name().dtor_value()));
    }
    builder.operations(ToNative.GrantOperationList(dafnyValue.dtor_Operations()));
    if (dafnyValue.dtor_RetiringPrincipal().is_Some()) {
      builder.retiringPrincipal(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RetiringPrincipal().dtor_value()));
    }
    return builder.build();
  }

  public static CreateGrantResponse CreateGrantResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse dafnyValue) {
    CreateGrantResponse.Builder builder = CreateGrantResponse.builder();
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_GrantToken().is_Some()) {
      builder.grantToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantToken().dtor_value()));
    }
    return builder.build();
  }

  public static CreateKeyRequest CreateKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest dafnyValue) {
    CreateKeyRequest.Builder builder = CreateKeyRequest.builder();
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegion().is_Some()) {
      builder.multiRegion((dafnyValue.dtor_MultiRegion().dtor_value()));
    }
    if (dafnyValue.dtor_Origin().is_Some()) {
      builder.origin(ToNative.OriginType(dafnyValue.dtor_Origin().dtor_value()));
    }
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return builder.build();
  }

  public static CreateKeyResponse CreateKeyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse dafnyValue) {
    CreateKeyResponse.Builder builder = CreateKeyResponse.builder();
    if (dafnyValue.dtor_KeyMetadata().is_Some()) {
      builder.keyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_KeyMetadata().dtor_value()));
    }
    return builder.build();
  }

  public static CustomerMasterKeySpec CustomerMasterKeySpec(
      software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec dafnyValue) {
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

  public static List<CustomKeyStoresListEntry> CustomKeyStoresList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::CustomKeyStoresListEntry);
  }

  public static CustomKeyStoresListEntry CustomKeyStoresListEntry(
      software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry dafnyValue) {
    CustomKeyStoresListEntry.Builder builder = CustomKeyStoresListEntry.builder();
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    if (dafnyValue.dtor_ConnectionErrorCode().is_Some()) {
      builder.connectionErrorCode(ToNative.ConnectionErrorCodeType(dafnyValue.dtor_ConnectionErrorCode().dtor_value()));
    }
    if (dafnyValue.dtor_ConnectionState().is_Some()) {
      builder.connectionState(ToNative.ConnectionStateType(dafnyValue.dtor_ConnectionState().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreName().is_Some()) {
      builder.customKeyStoreName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_TrustAnchorCertificate().is_Some()) {
      builder.trustAnchorCertificate(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TrustAnchorCertificate().dtor_value()));
    }
    return builder.build();
  }

  public static DataKeyPairSpec DataKeyPairSpec(
      software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec dafnyValue) {
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

  public static DataKeySpec DataKeySpec(
      software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec dafnyValue) {
    if (dafnyValue.is_AES__256()) {
      return DataKeySpec.AES_256;
    }
    if (dafnyValue.is_AES__128()) {
      return DataKeySpec.AES_128;
    }
    return DataKeySpec.fromValue(dafnyValue.toString());
  }

  public static DecryptRequest DecryptRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest dafnyValue) {
    DecryptRequest.Builder builder = DecryptRequest.builder();
    builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().toRawArray())));
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static DecryptResponse DecryptResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse dafnyValue) {
    DecryptResponse.Builder builder = DecryptResponse.builder();
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static DeleteAliasRequest DeleteAliasRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest dafnyValue) {
    DeleteAliasRequest.Builder builder = DeleteAliasRequest.builder();
    builder.aliasName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    return builder.build();
  }

  public static DeleteCustomKeyStoreRequest DeleteCustomKeyStoreRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest dafnyValue) {
    DeleteCustomKeyStoreRequest.Builder builder = DeleteCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static DeleteCustomKeyStoreResponse DeleteCustomKeyStoreResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse dafnyValue) {
    return DeleteCustomKeyStoreResponse.builder().build();
  }

  public static DeleteImportedKeyMaterialRequest DeleteImportedKeyMaterialRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest dafnyValue) {
    DeleteImportedKeyMaterialRequest.Builder builder = DeleteImportedKeyMaterialRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DescribeCustomKeyStoresRequest DescribeCustomKeyStoresRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest dafnyValue) {
    DescribeCustomKeyStoresRequest.Builder builder = DescribeCustomKeyStoresRequest.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreName().is_Some()) {
      builder.customKeyStoreName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeCustomKeyStoresResponse DescribeCustomKeyStoresResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse dafnyValue) {
    DescribeCustomKeyStoresResponse.Builder builder = DescribeCustomKeyStoresResponse.builder();
    if (dafnyValue.dtor_CustomKeyStores().is_Some()) {
      builder.customKeyStores(ToNative.CustomKeyStoresList(dafnyValue.dtor_CustomKeyStores().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeKeyRequest DescribeKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest dafnyValue) {
    DescribeKeyRequest.Builder builder = DescribeKeyRequest.builder();
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DescribeKeyResponse DescribeKeyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse dafnyValue) {
    DescribeKeyResponse.Builder builder = DescribeKeyResponse.builder();
    if (dafnyValue.dtor_KeyMetadata().is_Some()) {
      builder.keyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_KeyMetadata().dtor_value()));
    }
    return builder.build();
  }

  public static DisableKeyRequest DisableKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest dafnyValue) {
    DisableKeyRequest.Builder builder = DisableKeyRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DisableKeyRotationRequest DisableKeyRotationRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest dafnyValue) {
    DisableKeyRotationRequest.Builder builder = DisableKeyRotationRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static DisconnectCustomKeyStoreRequest DisconnectCustomKeyStoreRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest dafnyValue) {
    DisconnectCustomKeyStoreRequest.Builder builder = DisconnectCustomKeyStoreRequest.builder();
    builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return builder.build();
  }

  public static DisconnectCustomKeyStoreResponse DisconnectCustomKeyStoreResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse dafnyValue) {
    return DisconnectCustomKeyStoreResponse.builder().build();
  }

  public static EnableKeyRequest EnableKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest dafnyValue) {
    EnableKeyRequest.Builder builder = EnableKeyRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static EnableKeyRotationRequest EnableKeyRotationRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest dafnyValue) {
    EnableKeyRotationRequest.Builder builder = EnableKeyRotationRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static EncryptionAlgorithmSpec EncryptionAlgorithmSpec(
      software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec dafnyValue) {
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

  public static List<EncryptionAlgorithmSpec> EncryptionAlgorithmSpecList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::EncryptionAlgorithmSpec);
  }

  public static Map<String, String> EncryptionContextType(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static EncryptRequest EncryptRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest dafnyValue) {
    EncryptRequest.Builder builder = EncryptRequest.builder();
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().toRawArray())));
    return builder.build();
  }

  public static EncryptResponse EncryptResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse dafnyValue) {
    EncryptResponse.Builder builder = EncryptResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      builder.encryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static ExpirationModelType ExpirationModelType(
      software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType dafnyValue) {
    if (dafnyValue.is_KEY__MATERIAL__EXPIRES()) {
      return ExpirationModelType.KEY_MATERIAL_EXPIRES;
    }
    if (dafnyValue.is_KEY__MATERIAL__DOES__NOT__EXPIRE()) {
      return ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE;
    }
    return ExpirationModelType.fromValue(dafnyValue.toString());
  }

  public static GenerateDataKeyPairRequest GenerateDataKeyPairRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest dafnyValue) {
    GenerateDataKeyPairRequest.Builder builder = GenerateDataKeyPairRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    return builder.build();
  }

  public static GenerateDataKeyPairResponse GenerateDataKeyPairResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse dafnyValue) {
    GenerateDataKeyPairResponse.Builder builder = GenerateDataKeyPairResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyPairSpec().is_Some()) {
      builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec().dtor_value()));
    }
    if (dafnyValue.dtor_PrivateKeyCiphertextBlob().is_Some()) {
      builder.privateKeyCiphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyCiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PrivateKeyPlaintext().is_Some()) {
      builder.privateKeyPlaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyPlaintext().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GenerateDataKeyPairWithoutPlaintextRequest GenerateDataKeyPairWithoutPlaintextRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyPairWithoutPlaintextRequest.Builder builder = GenerateDataKeyPairWithoutPlaintextRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    return builder.build();
  }

  public static GenerateDataKeyPairWithoutPlaintextResponse GenerateDataKeyPairWithoutPlaintextResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse dafnyValue) {
    GenerateDataKeyPairWithoutPlaintextResponse.Builder builder = GenerateDataKeyPairWithoutPlaintextResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyPairSpec().is_Some()) {
      builder.keyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec().dtor_value()));
    }
    if (dafnyValue.dtor_PrivateKeyCiphertextBlob().is_Some()) {
      builder.privateKeyCiphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PrivateKeyCiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GenerateDataKeyRequest GenerateDataKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest dafnyValue) {
    GenerateDataKeyRequest.Builder builder = GenerateDataKeyRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyResponse GenerateDataKeyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse dafnyValue) {
    GenerateDataKeyResponse.Builder builder = GenerateDataKeyResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GenerateDataKeyWithoutPlaintextRequest GenerateDataKeyWithoutPlaintextRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyWithoutPlaintextRequest.Builder builder = GenerateDataKeyWithoutPlaintextRequest.builder();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      builder.encryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateDataKeyWithoutPlaintextResponse GenerateDataKeyWithoutPlaintextResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse dafnyValue) {
    GenerateDataKeyWithoutPlaintextResponse.Builder builder = GenerateDataKeyWithoutPlaintextResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateRandomRequest GenerateRandomRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest dafnyValue) {
    GenerateRandomRequest.Builder builder = GenerateRandomRequest.builder();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      builder.numberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    return builder.build();
  }

  public static GenerateRandomResponse GenerateRandomResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse dafnyValue) {
    GenerateRandomResponse.Builder builder = GenerateRandomResponse.builder();
    if (dafnyValue.dtor_Plaintext().is_Some()) {
      builder.plaintext(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Plaintext().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GetKeyPolicyRequest GetKeyPolicyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest dafnyValue) {
    GetKeyPolicyRequest.Builder builder = GetKeyPolicyRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.policyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    return builder.build();
  }

  public static GetKeyPolicyResponse GetKeyPolicyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse dafnyValue) {
    GetKeyPolicyResponse.Builder builder = GetKeyPolicyResponse.builder();
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    return builder.build();
  }

  public static GetKeyRotationStatusRequest GetKeyRotationStatusRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest dafnyValue) {
    GetKeyRotationStatusRequest.Builder builder = GetKeyRotationStatusRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static GetKeyRotationStatusResponse GetKeyRotationStatusResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse dafnyValue) {
    GetKeyRotationStatusResponse.Builder builder = GetKeyRotationStatusResponse.builder();
    if (dafnyValue.dtor_KeyRotationEnabled().is_Some()) {
      builder.keyRotationEnabled((dafnyValue.dtor_KeyRotationEnabled().dtor_value()));
    }
    return builder.build();
  }

  public static GetParametersForImportRequest GetParametersForImportRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest dafnyValue) {
    GetParametersForImportRequest.Builder builder = GetParametersForImportRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.wrappingAlgorithm(ToNative.AlgorithmSpec(dafnyValue.dtor_WrappingAlgorithm()));
    builder.wrappingKeySpec(ToNative.WrappingKeySpec(dafnyValue.dtor_WrappingKeySpec()));
    return builder.build();
  }

  public static GetParametersForImportResponse GetParametersForImportResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse dafnyValue) {
    GetParametersForImportResponse.Builder builder = GetParametersForImportResponse.builder();
    if (dafnyValue.dtor_ImportToken().is_Some()) {
      builder.importToken(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ImportToken().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ParametersValidTo().is_Some()) {
      builder.parametersValidTo(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ParametersValidTo().dtor_value()));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    return builder.build();
  }

  public static GetPublicKeyRequest GetPublicKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest dafnyValue) {
    GetPublicKeyRequest.Builder builder = GetPublicKeyRequest.builder();
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static GetPublicKeyResponse GetPublicKeyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse dafnyValue) {
    GetPublicKeyResponse.Builder builder = GetPublicKeyResponse.builder();
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithms().is_Some()) {
      builder.encryptionAlgorithms(ToNative.EncryptionAlgorithmSpecList(dafnyValue.dtor_EncryptionAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_PublicKey().is_Some()) {
      builder.publicKey(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_PublicKey().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_SigningAlgorithms().is_Some()) {
      builder.signingAlgorithms(ToNative.SigningAlgorithmSpecList(dafnyValue.dtor_SigningAlgorithms().dtor_value()));
    }
    return builder.build();
  }

  public static GrantConstraints GrantConstraints(
      software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints dafnyValue) {
    GrantConstraints.Builder builder = GrantConstraints.builder();
    if (dafnyValue.dtor_EncryptionContextEquals().is_Some()) {
      builder.encryptionContextEquals(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextEquals().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionContextSubset().is_Some()) {
      builder.encryptionContextSubset(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextSubset().dtor_value()));
    }
    return builder.build();
  }

  public static List<GrantListEntry> GrantList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::GrantListEntry);
  }

  public static GrantListEntry GrantListEntry(
      software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry dafnyValue) {
    GrantListEntry.Builder builder = GrantListEntry.builder();
    if (dafnyValue.dtor_Constraints().is_Some()) {
      builder.constraints(ToNative.GrantConstraints(dafnyValue.dtor_Constraints().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_GranteePrincipal().is_Some()) {
      builder.granteePrincipal(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_IssuingAccount().is_Some()) {
      builder.issuingAccount(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IssuingAccount().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Name().is_Some()) {
      builder.name(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Name().dtor_value()));
    }
    if (dafnyValue.dtor_Operations().is_Some()) {
      builder.operations(ToNative.GrantOperationList(dafnyValue.dtor_Operations().dtor_value()));
    }
    if (dafnyValue.dtor_RetiringPrincipal().is_Some()) {
      builder.retiringPrincipal(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RetiringPrincipal().dtor_value()));
    }
    return builder.build();
  }

  public static GrantOperation GrantOperation(
      software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation dafnyValue) {
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

  public static List<GrantOperation> GrantOperationList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::GrantOperation);
  }

  public static List<String> GrantTokenList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static ImportKeyMaterialRequest ImportKeyMaterialRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest dafnyValue) {
    ImportKeyMaterialRequest.Builder builder = ImportKeyMaterialRequest.builder();
    builder.encryptedKeyMaterial(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_EncryptedKeyMaterial().toRawArray())));
    if (dafnyValue.dtor_ExpirationModel().is_Some()) {
      builder.expirationModel(ToNative.ExpirationModelType(dafnyValue.dtor_ExpirationModel().dtor_value()));
    }
    builder.importToken(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ImportToken().toRawArray())));
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_ValidTo().is_Some()) {
      builder.validTo(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ValidTo().dtor_value()));
    }
    return builder.build();
  }

  public static ImportKeyMaterialResponse ImportKeyMaterialResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse dafnyValue) {
    return ImportKeyMaterialResponse.builder().build();
  }

  public static KeyManagerType KeyManagerType(
      software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType dafnyValue) {
    if (dafnyValue.is_AWS()) {
      return KeyManagerType.AWS;
    }
    if (dafnyValue.is_CUSTOMER()) {
      return KeyManagerType.CUSTOMER;
    }
    return KeyManagerType.fromValue(dafnyValue.toString());
  }

  public static KeyMetadata KeyMetadata(
      software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata dafnyValue) {
    KeyMetadata.Builder builder = KeyMetadata.builder();
    if (dafnyValue.dtor_Arn().is_Some()) {
      builder.arn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Arn().dtor_value()));
    }
    if (dafnyValue.dtor_AWSAccountId().is_Some()) {
      builder.awsAccountId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AWSAccountId().dtor_value()));
    }
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDate().is_Some()) {
      builder.creationDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDate().dtor_value()));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      builder.customerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_DeletionDate().is_Some()) {
      builder.deletionDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_DeletionDate().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_Enabled().is_Some()) {
      builder.enabled((dafnyValue.dtor_Enabled().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithms().is_Some()) {
      builder.encryptionAlgorithms(ToNative.EncryptionAlgorithmSpecList(dafnyValue.dtor_EncryptionAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_ExpirationModel().is_Some()) {
      builder.expirationModel(ToNative.ExpirationModelType(dafnyValue.dtor_ExpirationModel().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_KeyManager().is_Some()) {
      builder.keyManager(ToNative.KeyManagerType(dafnyValue.dtor_KeyManager().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      builder.keySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeyState().is_Some()) {
      builder.keyState(ToNative.KeyState(dafnyValue.dtor_KeyState().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      builder.keyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegion().is_Some()) {
      builder.multiRegion((dafnyValue.dtor_MultiRegion().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegionConfiguration().is_Some()) {
      builder.multiRegionConfiguration(ToNative.MultiRegionConfiguration(dafnyValue.dtor_MultiRegionConfiguration().dtor_value()));
    }
    if (dafnyValue.dtor_Origin().is_Some()) {
      builder.origin(ToNative.OriginType(dafnyValue.dtor_Origin().dtor_value()));
    }
    if (dafnyValue.dtor_PendingDeletionWindowInDays().is_Some()) {
      builder.pendingDeletionWindowInDays((dafnyValue.dtor_PendingDeletionWindowInDays().dtor_value()));
    }
    if (dafnyValue.dtor_SigningAlgorithms().is_Some()) {
      builder.signingAlgorithms(ToNative.SigningAlgorithmSpecList(dafnyValue.dtor_SigningAlgorithms().dtor_value()));
    }
    if (dafnyValue.dtor_ValidTo().is_Some()) {
      builder.validTo(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ValidTo().dtor_value()));
    }
    return builder.build();
  }

  public static KeySpec KeySpec(
      software.amazon.cryptography.services.kms.internaldafny.types.KeySpec dafnyValue) {
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

  public static KeyState KeyState(
      software.amazon.cryptography.services.kms.internaldafny.types.KeyState dafnyValue) {
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

  public static KeyUsageType KeyUsageType(
      software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType dafnyValue) {
    if (dafnyValue.is_SIGN__VERIFY()) {
      return KeyUsageType.SIGN_VERIFY;
    }
    if (dafnyValue.is_ENCRYPT__DECRYPT()) {
      return KeyUsageType.ENCRYPT_DECRYPT;
    }
    return KeyUsageType.fromValue(dafnyValue.toString());
  }

  public static ListAliasesRequest ListAliasesRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest dafnyValue) {
    ListAliasesRequest.Builder builder = ListAliasesRequest.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListAliasesResponse ListAliasesResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse dafnyValue) {
    ListAliasesResponse.Builder builder = ListAliasesResponse.builder();
    if (dafnyValue.dtor_Aliases().is_Some()) {
      builder.aliases(ToNative.AliasList(dafnyValue.dtor_Aliases().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListGrantsRequest ListGrantsRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest dafnyValue) {
    ListGrantsRequest.Builder builder = ListGrantsRequest.builder();
    if (dafnyValue.dtor_GranteePrincipal().is_Some()) {
      builder.granteePrincipal(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListGrantsResponse ListGrantsResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse dafnyValue) {
    ListGrantsResponse.Builder builder = ListGrantsResponse.builder();
    if (dafnyValue.dtor_Grants().is_Some()) {
      builder.grants(ToNative.GrantList(dafnyValue.dtor_Grants().dtor_value()));
    }
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListKeyPoliciesRequest ListKeyPoliciesRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest dafnyValue) {
    ListKeyPoliciesRequest.Builder builder = ListKeyPoliciesRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListKeyPoliciesResponse ListKeyPoliciesResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse dafnyValue) {
    ListKeyPoliciesResponse.Builder builder = ListKeyPoliciesResponse.builder();
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_PolicyNames().is_Some()) {
      builder.policyNames(ToNative.PolicyNameList(dafnyValue.dtor_PolicyNames().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static ListResourceTagsRequest ListResourceTagsRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest dafnyValue) {
    ListResourceTagsRequest.Builder builder = ListResourceTagsRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      builder.marker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return builder.build();
  }

  public static ListResourceTagsResponse ListResourceTagsResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse dafnyValue) {
    ListResourceTagsResponse.Builder builder = ListResourceTagsResponse.builder();
    if (dafnyValue.dtor_NextMarker().is_Some()) {
      builder.nextMarker(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextMarker().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_Truncated().is_Some()) {
      builder.truncated((dafnyValue.dtor_Truncated().dtor_value()));
    }
    return builder.build();
  }

  public static MessageType MessageType(
      software.amazon.cryptography.services.kms.internaldafny.types.MessageType dafnyValue) {
    if (dafnyValue.is_RAW()) {
      return MessageType.RAW;
    }
    if (dafnyValue.is_DIGEST()) {
      return MessageType.DIGEST;
    }
    return MessageType.fromValue(dafnyValue.toString());
  }

  public static MultiRegionConfiguration MultiRegionConfiguration(
      software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration dafnyValue) {
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

  public static MultiRegionKey MultiRegionKey(
      software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey dafnyValue) {
    MultiRegionKey.Builder builder = MultiRegionKey.builder();
    if (dafnyValue.dtor_Arn().is_Some()) {
      builder.arn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Arn().dtor_value()));
    }
    if (dafnyValue.dtor_Region().is_Some()) {
      builder.region(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Region().dtor_value()));
    }
    return builder.build();
  }

  public static List<MultiRegionKey> MultiRegionKeyList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::MultiRegionKey);
  }

  public static MultiRegionKeyType MultiRegionKeyType(
      software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType dafnyValue) {
    if (dafnyValue.is_PRIMARY()) {
      return MultiRegionKeyType.PRIMARY;
    }
    if (dafnyValue.is_REPLICA()) {
      return MultiRegionKeyType.REPLICA;
    }
    return MultiRegionKeyType.fromValue(dafnyValue.toString());
  }

  public static OriginType OriginType(
      software.amazon.cryptography.services.kms.internaldafny.types.OriginType dafnyValue) {
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

  public static List<String> PolicyNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static PutKeyPolicyRequest PutKeyPolicyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest dafnyValue) {
    PutKeyPolicyRequest.Builder builder = PutKeyPolicyRequest.builder();
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.policy(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy()));
    builder.policyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    return builder.build();
  }

  public static ReEncryptRequest ReEncryptRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest dafnyValue) {
    ReEncryptRequest.Builder builder = ReEncryptRequest.builder();
    builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().toRawArray())));
    if (dafnyValue.dtor_DestinationEncryptionAlgorithm().is_Some()) {
      builder.destinationEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_DestinationEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationEncryptionContext().is_Some()) {
      builder.destinationEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_DestinationEncryptionContext().dtor_value()));
    }
    builder.destinationKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_DestinationKeyId()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionAlgorithm().is_Some()) {
      builder.sourceEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_SourceEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionContext().is_Some()) {
      builder.sourceEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_SourceEncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_SourceKeyId().is_Some()) {
      builder.sourceKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceKeyId().dtor_value()));
    }
    return builder.build();
  }

  public static ReEncryptResponse ReEncryptResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse dafnyValue) {
    ReEncryptResponse.Builder builder = ReEncryptResponse.builder();
    if (dafnyValue.dtor_CiphertextBlob().is_Some()) {
      builder.ciphertextBlob(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_CiphertextBlob().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_DestinationEncryptionAlgorithm().is_Some()) {
      builder.destinationEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_DestinationEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionAlgorithm().is_Some()) {
      builder.sourceEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_SourceEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_SourceKeyId().is_Some()) {
      builder.sourceKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceKeyId().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicateKeyRequest ReplicateKeyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest dafnyValue) {
    ReplicateKeyRequest.Builder builder = ReplicateKeyRequest.builder();
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      builder.bypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      builder.description(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Policy().is_Some()) {
      builder.policy(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    builder.replicaRegion(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaRegion()));
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicateKeyResponse ReplicateKeyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse dafnyValue) {
    ReplicateKeyResponse.Builder builder = ReplicateKeyResponse.builder();
    if (dafnyValue.dtor_ReplicaKeyMetadata().is_Some()) {
      builder.replicaKeyMetadata(ToNative.KeyMetadata(dafnyValue.dtor_ReplicaKeyMetadata().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaPolicy().is_Some()) {
      builder.replicaPolicy(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaPolicy().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTags().is_Some()) {
      builder.replicaTags(ToNative.TagList(dafnyValue.dtor_ReplicaTags().dtor_value()));
    }
    return builder.build();
  }

  public static RetireGrantRequest RetireGrantRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest dafnyValue) {
    RetireGrantRequest.Builder builder = RetireGrantRequest.builder();
    if (dafnyValue.dtor_GrantId().is_Some()) {
      builder.grantId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_GrantToken().is_Some()) {
      builder.grantToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantToken().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    return builder.build();
  }

  public static RevokeGrantRequest RevokeGrantRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest dafnyValue) {
    RevokeGrantRequest.Builder builder = RevokeGrantRequest.builder();
    builder.grantId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId()));
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static ScheduleKeyDeletionRequest ScheduleKeyDeletionRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest dafnyValue) {
    ScheduleKeyDeletionRequest.Builder builder = ScheduleKeyDeletionRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_PendingWindowInDays().is_Some()) {
      builder.pendingWindowInDays((dafnyValue.dtor_PendingWindowInDays().dtor_value()));
    }
    return builder.build();
  }

  public static ScheduleKeyDeletionResponse ScheduleKeyDeletionResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse dafnyValue) {
    ScheduleKeyDeletionResponse.Builder builder = ScheduleKeyDeletionResponse.builder();
    if (dafnyValue.dtor_DeletionDate().is_Some()) {
      builder.deletionDate(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_DeletionDate().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_KeyState().is_Some()) {
      builder.keyState(ToNative.KeyState(dafnyValue.dtor_KeyState().dtor_value()));
    }
    if (dafnyValue.dtor_PendingWindowInDays().is_Some()) {
      builder.pendingWindowInDays((dafnyValue.dtor_PendingWindowInDays().dtor_value()));
    }
    return builder.build();
  }

  public static SigningAlgorithmSpec SigningAlgorithmSpec(
      software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec dafnyValue) {
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

  public static List<SigningAlgorithmSpec> SigningAlgorithmSpecList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::SigningAlgorithmSpec);
  }

  public static SignRequest SignRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.SignRequest dafnyValue) {
    SignRequest.Builder builder = SignRequest.builder();
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.message(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Message().toRawArray())));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      builder.messageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    return builder.build();
  }

  public static SignResponse SignResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.SignResponse dafnyValue) {
    SignResponse.Builder builder = SignResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Signature().is_Some()) {
      builder.signature(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Signature().dtor_value().toRawArray())));
    }
    if (dafnyValue.dtor_SigningAlgorithm().is_Some()) {
      builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static Tag Tag(
      software.amazon.cryptography.services.kms.internaldafny.types.Tag dafnyValue) {
    Tag.Builder builder = Tag.builder();
    builder.tagKey(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagKey()));
    builder.tagValue(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagValue()));
    return builder.build();
  }

  public static List<String> TagKeyList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<Tag> TagList(
      DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.Tag> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.kms.internaldafny.ToNative::Tag);
  }

  public static TagResourceRequest TagResourceRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest dafnyValue) {
    TagResourceRequest.Builder builder = TagResourceRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.tags(ToNative.TagList(dafnyValue.dtor_Tags()));
    return builder.build();
  }

  public static UntagResourceRequest UntagResourceRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest dafnyValue) {
    UntagResourceRequest.Builder builder = UntagResourceRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.tagKeys(ToNative.TagKeyList(dafnyValue.dtor_TagKeys()));
    return builder.build();
  }

  public static UpdateAliasRequest UpdateAliasRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest dafnyValue) {
    UpdateAliasRequest.Builder builder = UpdateAliasRequest.builder();
    builder.aliasName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    builder.targetKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return builder.build();
  }

  public static UpdateCustomKeyStoreRequest UpdateCustomKeyStoreRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest dafnyValue) {
    UpdateCustomKeyStoreRequest.Builder builder = UpdateCustomKeyStoreRequest.builder();
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      builder.cloudHsmClusterId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    builder.customKeyStoreId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    if (dafnyValue.dtor_KeyStorePassword().is_Some()) {
      builder.keyStorePassword(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword().dtor_value()));
    }
    if (dafnyValue.dtor_NewCustomKeyStoreName().is_Some()) {
      builder.newCustomKeyStoreName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NewCustomKeyStoreName().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateCustomKeyStoreResponse UpdateCustomKeyStoreResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse dafnyValue) {
    return UpdateCustomKeyStoreResponse.builder().build();
  }

  public static UpdateKeyDescriptionRequest UpdateKeyDescriptionRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest dafnyValue) {
    UpdateKeyDescriptionRequest.Builder builder = UpdateKeyDescriptionRequest.builder();
    builder.description(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description()));
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return builder.build();
  }

  public static UpdatePrimaryRegionRequest UpdatePrimaryRegionRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest dafnyValue) {
    UpdatePrimaryRegionRequest.Builder builder = UpdatePrimaryRegionRequest.builder();
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.primaryRegion(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PrimaryRegion()));
    return builder.build();
  }

  public static VerifyRequest VerifyRequest(
      software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest dafnyValue) {
    VerifyRequest.Builder builder = VerifyRequest.builder();
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      builder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    builder.message(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Message().toRawArray())));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      builder.messageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    builder.signature(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_Signature().toRawArray())));
    builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    return builder.build();
  }

  public static VerifyResponse VerifyResponse(
      software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse dafnyValue) {
    VerifyResponse.Builder builder = VerifyResponse.builder();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      builder.keyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_SignatureValid().is_Some()) {
      builder.signatureValid((dafnyValue.dtor_SignatureValid().dtor_value()));
    }
    if (dafnyValue.dtor_SigningAlgorithm().is_Some()) {
      builder.signingAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm().dtor_value()));
    }
    return builder.build();
  }

  public static WrappingKeySpec WrappingKeySpec(
      software.amazon.cryptography.services.kms.internaldafny.types.WrappingKeySpec dafnyValue) {
    if (dafnyValue.is_RSA__2048()) {
      return WrappingKeySpec.RSA_2048;
    }
    return WrappingKeySpec.fromValue(dafnyValue.toString());
  }

  public static AlreadyExistsException Error(Error_AlreadyExistsException dafnyValue) {
    AlreadyExistsException.Builder builder = AlreadyExistsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterInUseException Error(
      Error_CloudHsmClusterInUseException dafnyValue) {
    CloudHsmClusterInUseException.Builder builder = CloudHsmClusterInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterInvalidConfigurationException Error(
      Error_CloudHsmClusterInvalidConfigurationException dafnyValue) {
    CloudHsmClusterInvalidConfigurationException.Builder builder = CloudHsmClusterInvalidConfigurationException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotActiveException Error(
      Error_CloudHsmClusterNotActiveException dafnyValue) {
    CloudHsmClusterNotActiveException.Builder builder = CloudHsmClusterNotActiveException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotFoundException Error(
      Error_CloudHsmClusterNotFoundException dafnyValue) {
    CloudHsmClusterNotFoundException.Builder builder = CloudHsmClusterNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CloudHsmClusterNotRelatedException Error(
      Error_CloudHsmClusterNotRelatedException dafnyValue) {
    CloudHsmClusterNotRelatedException.Builder builder = CloudHsmClusterNotRelatedException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreHasCmKsException Error(
      Error_CustomKeyStoreHasCMKsException dafnyValue) {
    CustomKeyStoreHasCmKsException.Builder builder = CustomKeyStoreHasCmKsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreInvalidStateException Error(
      Error_CustomKeyStoreInvalidStateException dafnyValue) {
    CustomKeyStoreInvalidStateException.Builder builder = CustomKeyStoreInvalidStateException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreNameInUseException Error(
      Error_CustomKeyStoreNameInUseException dafnyValue) {
    CustomKeyStoreNameInUseException.Builder builder = CustomKeyStoreNameInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static CustomKeyStoreNotFoundException Error(
      Error_CustomKeyStoreNotFoundException dafnyValue) {
    CustomKeyStoreNotFoundException.Builder builder = CustomKeyStoreNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static DependencyTimeoutException Error(Error_DependencyTimeoutException dafnyValue) {
    DependencyTimeoutException.Builder builder = DependencyTimeoutException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static DisabledException Error(Error_DisabledException dafnyValue) {
    DisabledException.Builder builder = DisabledException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ExpiredImportTokenException Error(Error_ExpiredImportTokenException dafnyValue) {
    ExpiredImportTokenException.Builder builder = ExpiredImportTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectKeyException Error(Error_IncorrectKeyException dafnyValue) {
    IncorrectKeyException.Builder builder = IncorrectKeyException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectKeyMaterialException Error(
      Error_IncorrectKeyMaterialException dafnyValue) {
    IncorrectKeyMaterialException.Builder builder = IncorrectKeyMaterialException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IncorrectTrustAnchorException Error(
      Error_IncorrectTrustAnchorException dafnyValue) {
    IncorrectTrustAnchorException.Builder builder = IncorrectTrustAnchorException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidAliasNameException Error(Error_InvalidAliasNameException dafnyValue) {
    InvalidAliasNameException.Builder builder = InvalidAliasNameException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidArnException Error(Error_InvalidArnException dafnyValue) {
    InvalidArnException.Builder builder = InvalidArnException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidCiphertextException Error(Error_InvalidCiphertextException dafnyValue) {
    InvalidCiphertextException.Builder builder = InvalidCiphertextException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidGrantIdException Error(Error_InvalidGrantIdException dafnyValue) {
    InvalidGrantIdException.Builder builder = InvalidGrantIdException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidGrantTokenException Error(Error_InvalidGrantTokenException dafnyValue) {
    InvalidGrantTokenException.Builder builder = InvalidGrantTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidImportTokenException Error(Error_InvalidImportTokenException dafnyValue) {
    InvalidImportTokenException.Builder builder = InvalidImportTokenException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidKeyUsageException Error(Error_InvalidKeyUsageException dafnyValue) {
    InvalidKeyUsageException.Builder builder = InvalidKeyUsageException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidMarkerException Error(Error_InvalidMarkerException dafnyValue) {
    InvalidMarkerException.Builder builder = InvalidMarkerException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KeyUnavailableException Error(Error_KeyUnavailableException dafnyValue) {
    KeyUnavailableException.Builder builder = KeyUnavailableException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInternalException Error(Error_KMSInternalException dafnyValue) {
    KmsInternalException.Builder builder = KmsInternalException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInvalidSignatureException Error(Error_KMSInvalidSignatureException dafnyValue) {
    KmsInvalidSignatureException.Builder builder = KmsInvalidSignatureException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static KmsInvalidStateException Error(Error_KMSInvalidStateException dafnyValue) {
    KmsInvalidStateException.Builder builder = KmsInvalidStateException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static LimitExceededException Error(Error_LimitExceededException dafnyValue) {
    LimitExceededException.Builder builder = LimitExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static MalformedPolicyDocumentException Error(
      Error_MalformedPolicyDocumentException dafnyValue) {
    MalformedPolicyDocumentException.Builder builder = MalformedPolicyDocumentException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static NotFoundException Error(Error_NotFoundException dafnyValue) {
    NotFoundException.Builder builder = NotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TagException Error(Error_TagException dafnyValue) {
    TagException.Builder builder = TagException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static UnsupportedOperationException Error(
      Error_UnsupportedOperationException dafnyValue) {
    UnsupportedOperationException.Builder builder = UnsupportedOperationException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  // BEGIN MANUAL EDIT
  public static RuntimeException Error(software.amazon.cryptography.services.kms.internaldafny.types.Error dafnyValue) {
    if (dafnyValue.is_AlreadyExistsException()) {
      return ToNative.Error((Error_AlreadyExistsException) dafnyValue);
    }
    if (dafnyValue.is_CloudHsmClusterInUseException()) {
      return ToNative.Error((Error_CloudHsmClusterInUseException) dafnyValue);
    }
    if (dafnyValue.is_CloudHsmClusterInvalidConfigurationException()) {
      return ToNative.Error((Error_CloudHsmClusterInvalidConfigurationException) dafnyValue);
    }
    if (dafnyValue.is_CloudHsmClusterNotActiveException()) {
      return ToNative.Error((Error_CloudHsmClusterNotActiveException) dafnyValue);
    }
    if (dafnyValue.is_CloudHsmClusterNotFoundException()) {
      return ToNative.Error((Error_CloudHsmClusterNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_CloudHsmClusterNotRelatedException()) {
      return ToNative.Error((Error_CloudHsmClusterNotRelatedException) dafnyValue);
    }
    if (dafnyValue.is_CustomKeyStoreHasCMKsException()) {
      return ToNative.Error((Error_CustomKeyStoreHasCMKsException) dafnyValue);
    }
    if (dafnyValue.is_CustomKeyStoreInvalidStateException()) {
      return ToNative.Error((Error_CustomKeyStoreInvalidStateException) dafnyValue);
    }
    if (dafnyValue.is_CustomKeyStoreNameInUseException()) {
      return ToNative.Error((Error_CustomKeyStoreNameInUseException) dafnyValue);
    }
    if (dafnyValue.is_CustomKeyStoreNotFoundException()) {
      return ToNative.Error((Error_CustomKeyStoreNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_DependencyTimeoutException()) {
      return ToNative.Error((Error_DependencyTimeoutException) dafnyValue);
    }
    if (dafnyValue.is_DisabledException()) {
      return ToNative.Error((Error_DisabledException) dafnyValue);
    }
    if (dafnyValue.is_ExpiredImportTokenException()) {
      return ToNative.Error((Error_ExpiredImportTokenException) dafnyValue);
    }
    if (dafnyValue.is_IncorrectKeyException()) {
      return ToNative.Error((Error_IncorrectKeyException) dafnyValue);
    }
    if (dafnyValue.is_IncorrectKeyMaterialException()) {
      return ToNative.Error((Error_IncorrectKeyMaterialException) dafnyValue);
    }
    if (dafnyValue.is_IncorrectTrustAnchorException()) {
      return ToNative.Error((Error_IncorrectTrustAnchorException) dafnyValue);
    }
    if (dafnyValue.is_InvalidAliasNameException()) {
      return ToNative.Error((Error_InvalidAliasNameException) dafnyValue);
    }
    if (dafnyValue.is_InvalidArnException()) {
      return ToNative.Error((Error_InvalidArnException) dafnyValue);
    }
    if (dafnyValue.is_InvalidCiphertextException()) {
      return ToNative.Error((Error_InvalidCiphertextException) dafnyValue);
    }
    if (dafnyValue.is_InvalidGrantIdException()) {
      return ToNative.Error((Error_InvalidGrantIdException) dafnyValue);
    }
    if (dafnyValue.is_InvalidGrantTokenException()) {
      return ToNative.Error((Error_InvalidGrantTokenException) dafnyValue);
    }
    if (dafnyValue.is_InvalidImportTokenException()) {
      return ToNative.Error((Error_InvalidImportTokenException) dafnyValue);
    }
    if (dafnyValue.is_InvalidKeyUsageException()) {
      return ToNative.Error((Error_InvalidKeyUsageException) dafnyValue);
    }
    if (dafnyValue.is_InvalidMarkerException()) {
      return ToNative.Error((Error_InvalidMarkerException) dafnyValue);
    }
    if (dafnyValue.is_KeyUnavailableException()) {
      return ToNative.Error((Error_KeyUnavailableException) dafnyValue);
    }
    if (dafnyValue.is_KMSInternalException()) {
      return ToNative.Error((Error_KMSInternalException) dafnyValue);
    }
    if (dafnyValue.is_KMSInvalidSignatureException()) {
      return ToNative.Error((Error_KMSInvalidSignatureException) dafnyValue);
    }
    if (dafnyValue.is_KMSInvalidStateException()) {
      return ToNative.Error((Error_KMSInvalidStateException) dafnyValue);
    }
    if (dafnyValue.is_LimitExceededException()) {
      return ToNative.Error((Error_LimitExceededException) dafnyValue);
    }
    if (dafnyValue.is_MalformedPolicyDocumentException()) {
      return ToNative.Error((Error_MalformedPolicyDocumentException) dafnyValue);
    }
    if (dafnyValue.is_NotFoundException()) {
      return ToNative.Error((Error_NotFoundException) dafnyValue);
    }
    if (dafnyValue.is_TagException()) {
      return ToNative.Error((Error_TagException) dafnyValue);
    }
    if (dafnyValue.is_UnsupportedOperationException()) {
      return ToNative.Error((Error_UnsupportedOperationException) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    // TODO This should indicate a codegen bug
    return new IllegalStateException("Unknown error recieved from KMS.");
  }
// END MANUAL EDIT

  public static KmsClient TrentService(IKMSClient dafnyValue) {
    return ((Shim) dafnyValue).impl();
  }
}
