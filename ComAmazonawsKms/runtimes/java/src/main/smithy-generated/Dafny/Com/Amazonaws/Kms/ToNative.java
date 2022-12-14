// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package Dafny.Com.Amazonaws.Kms;

import com.amazonaws.services.kms.model.AlgorithmSpec;
import com.amazonaws.services.kms.model.CancelKeyDeletionRequest;
import com.amazonaws.services.kms.model.ConnectCustomKeyStoreRequest;
import com.amazonaws.services.kms.model.CreateAliasRequest;
import com.amazonaws.services.kms.model.CreateCustomKeyStoreRequest;
import com.amazonaws.services.kms.model.CreateGrantRequest;
import com.amazonaws.services.kms.model.CreateKeyRequest;
import com.amazonaws.services.kms.model.CustomerMasterKeySpec;
import com.amazonaws.services.kms.model.DataKeyPairSpec;
import com.amazonaws.services.kms.model.DataKeySpec;
import com.amazonaws.services.kms.model.DecryptRequest;
import com.amazonaws.services.kms.model.DeleteAliasRequest;
import com.amazonaws.services.kms.model.DeleteCustomKeyStoreRequest;
import com.amazonaws.services.kms.model.DeleteImportedKeyMaterialRequest;
import com.amazonaws.services.kms.model.DescribeCustomKeyStoresRequest;
import com.amazonaws.services.kms.model.DescribeKeyRequest;
import com.amazonaws.services.kms.model.DisableKeyRequest;
import com.amazonaws.services.kms.model.DisableKeyRotationRequest;
import com.amazonaws.services.kms.model.DisconnectCustomKeyStoreRequest;
import com.amazonaws.services.kms.model.EnableKeyRequest;
import com.amazonaws.services.kms.model.EnableKeyRotationRequest;
import com.amazonaws.services.kms.model.EncryptRequest;
import com.amazonaws.services.kms.model.EncryptionAlgorithmSpec;
import com.amazonaws.services.kms.model.ExpirationModelType;
import com.amazonaws.services.kms.model.GenerateDataKeyPairRequest;
import com.amazonaws.services.kms.model.GenerateDataKeyPairWithoutPlaintextRequest;
import com.amazonaws.services.kms.model.GenerateDataKeyRequest;
import com.amazonaws.services.kms.model.GenerateDataKeyWithoutPlaintextRequest;
import com.amazonaws.services.kms.model.GenerateRandomRequest;
import com.amazonaws.services.kms.model.GetKeyPolicyRequest;
import com.amazonaws.services.kms.model.GetKeyRotationStatusRequest;
import com.amazonaws.services.kms.model.GetParametersForImportRequest;
import com.amazonaws.services.kms.model.GetPublicKeyRequest;
import com.amazonaws.services.kms.model.GrantConstraints;
import com.amazonaws.services.kms.model.GrantOperation;
import com.amazonaws.services.kms.model.ImportKeyMaterialRequest;
import com.amazonaws.services.kms.model.KeySpec;
import com.amazonaws.services.kms.model.KeyUsageType;
import com.amazonaws.services.kms.model.ListAliasesRequest;
import com.amazonaws.services.kms.model.ListGrantsRequest;
import com.amazonaws.services.kms.model.ListKeyPoliciesRequest;
import com.amazonaws.services.kms.model.ListResourceTagsRequest;
import com.amazonaws.services.kms.model.MessageType;
import com.amazonaws.services.kms.model.OriginType;
import com.amazonaws.services.kms.model.PutKeyPolicyRequest;
import com.amazonaws.services.kms.model.ReEncryptRequest;
import com.amazonaws.services.kms.model.ReplicateKeyRequest;
import com.amazonaws.services.kms.model.RetireGrantRequest;
import com.amazonaws.services.kms.model.RevokeGrantRequest;
import com.amazonaws.services.kms.model.ScheduleKeyDeletionRequest;
import com.amazonaws.services.kms.model.SignRequest;
import com.amazonaws.services.kms.model.SigningAlgorithmSpec;
import com.amazonaws.services.kms.model.Tag;
import com.amazonaws.services.kms.model.TagResourceRequest;
import com.amazonaws.services.kms.model.UntagResourceRequest;
import com.amazonaws.services.kms.model.UpdateAliasRequest;
import com.amazonaws.services.kms.model.UpdateCustomKeyStoreRequest;
import com.amazonaws.services.kms.model.UpdateKeyDescriptionRequest;
import com.amazonaws.services.kms.model.UpdatePrimaryRegionRequest;
import com.amazonaws.services.kms.model.VerifyRequest;
import com.amazonaws.services.kms.model.WrappingKeySpec;
import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Character;
import java.lang.String;
import java.util.List;
import java.util.Map;

public class ToNative {
  public static CancelKeyDeletionRequest CancelKeyDeletionRequest(
      Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionRequest dafnyValue) {
    CancelKeyDeletionRequest converted = new CancelKeyDeletionRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static ConnectCustomKeyStoreRequest ConnectCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreRequest dafnyValue) {
    ConnectCustomKeyStoreRequest converted = new ConnectCustomKeyStoreRequest();
    converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return converted;
  }

  public static CreateAliasRequest CreateAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateAliasRequest dafnyValue) {
    CreateAliasRequest converted = new CreateAliasRequest();
    converted.withAliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    converted.withTargetKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return converted;
  }

  public static CreateCustomKeyStoreRequest CreateCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreRequest dafnyValue) {
    CreateCustomKeyStoreRequest converted = new CreateCustomKeyStoreRequest();
    converted.withCustomKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName()));
    converted.withCloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId()));
    converted.withTrustAnchorCertificate(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TrustAnchorCertificate()));
    converted.withKeyStorePassword(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword()));
    return converted;
  }

  public static CreateGrantRequest CreateGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateGrantRequest dafnyValue) {
    CreateGrantRequest converted = new CreateGrantRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withGranteePrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal()));
    if (dafnyValue.dtor_RetiringPrincipal().is_Some()) {
      converted.withRetiringPrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RetiringPrincipal().dtor_value()));
    }
    GrantOperation[] operations_temp = new GrantOperation[dafnyValue.dtor_Operations().length()];
    converted.withOperations(ToNative.GrantOperationList(dafnyValue.dtor_Operations()).toArray(operations_temp));
    if (dafnyValue.dtor_Constraints().is_Some()) {
      converted.withConstraints(ToNative.GrantConstraints(dafnyValue.dtor_Constraints().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_Name().is_Some()) {
      converted.withName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Name().dtor_value()));
    }
    return converted;
  }

  public static CreateKeyRequest CreateKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.CreateKeyRequest dafnyValue) {
    CreateKeyRequest converted = new CreateKeyRequest();
    if (dafnyValue.dtor_Policy().is_Some()) {
      converted.withPolicy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      converted.withDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_KeyUsage().is_Some()) {
      converted.withKeyUsage(ToNative.KeyUsageType(dafnyValue.dtor_KeyUsage().dtor_value()));
    }
    if (dafnyValue.dtor_CustomerMasterKeySpec().is_Some()) {
      converted.withCustomerMasterKeySpec(ToNative.CustomerMasterKeySpec(dafnyValue.dtor_CustomerMasterKeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      converted.withKeySpec(ToNative.KeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_Origin().is_Some()) {
      converted.withOrigin(ToNative.OriginType(dafnyValue.dtor_Origin().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      converted.withBypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      converted.withTags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_MultiRegion().is_Some()) {
      converted.withMultiRegion((dafnyValue.dtor_MultiRegion().dtor_value()));
    }
    return converted;
  }

  public static DecryptRequest DecryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.DecryptRequest dafnyValue) {
    DecryptRequest converted = new DecryptRequest();
    converted.withCiphertextBlob(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_CiphertextBlob()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      converted.withEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return converted;
  }

  public static DeleteAliasRequest DeleteAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteAliasRequest dafnyValue) {
    DeleteAliasRequest converted = new DeleteAliasRequest();
    converted.withAliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    return converted;
  }

  public static DeleteCustomKeyStoreRequest DeleteCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreRequest dafnyValue) {
    DeleteCustomKeyStoreRequest converted = new DeleteCustomKeyStoreRequest();
    converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return converted;
  }

  public static DeleteImportedKeyMaterialRequest DeleteImportedKeyMaterialRequest(
      Dafny.Com.Amazonaws.Kms.Types.DeleteImportedKeyMaterialRequest dafnyValue) {
    DeleteImportedKeyMaterialRequest converted = new DeleteImportedKeyMaterialRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static DescribeCustomKeyStoresRequest DescribeCustomKeyStoresRequest(
      Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresRequest dafnyValue) {
    DescribeCustomKeyStoresRequest converted = new DescribeCustomKeyStoresRequest();
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreName().is_Some()) {
      converted.withCustomKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.withLimit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      converted.withMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return converted;
  }

  public static DescribeKeyRequest DescribeKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.DescribeKeyRequest dafnyValue) {
    DescribeKeyRequest converted = new DescribeKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static DisableKeyRequest DisableKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisableKeyRequest dafnyValue) {
    DisableKeyRequest converted = new DisableKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static DisableKeyRotationRequest DisableKeyRotationRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisableKeyRotationRequest dafnyValue) {
    DisableKeyRotationRequest converted = new DisableKeyRotationRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static DisconnectCustomKeyStoreRequest DisconnectCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreRequest dafnyValue) {
    DisconnectCustomKeyStoreRequest converted = new DisconnectCustomKeyStoreRequest();
    converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    return converted;
  }

  public static EnableKeyRequest EnableKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.EnableKeyRequest dafnyValue) {
    EnableKeyRequest converted = new EnableKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static EnableKeyRotationRequest EnableKeyRotationRequest(
      Dafny.Com.Amazonaws.Kms.Types.EnableKeyRotationRequest dafnyValue) {
    EnableKeyRotationRequest converted = new EnableKeyRotationRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static EncryptRequest EncryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.EncryptRequest dafnyValue) {
    EncryptRequest converted = new EncryptRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withPlaintext(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_Plaintext()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionAlgorithm().is_Some()) {
      converted.withEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_EncryptionAlgorithm().dtor_value()));
    }
    return converted;
  }

  public static GenerateDataKeyRequest GenerateDataKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyRequest dafnyValue) {
    GenerateDataKeyRequest converted = new GenerateDataKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      converted.withNumberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      converted.withKeySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static GenerateDataKeyPairRequest GenerateDataKeyPairRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairRequest dafnyValue) {
    GenerateDataKeyPairRequest converted = new GenerateDataKeyPairRequest();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withKeyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static GenerateDataKeyPairWithoutPlaintextRequest GenerateDataKeyPairWithoutPlaintextRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyPairWithoutPlaintextRequest converted = new GenerateDataKeyPairWithoutPlaintextRequest();
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withKeyPairSpec(ToNative.DataKeyPairSpec(dafnyValue.dtor_KeyPairSpec()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static GenerateDataKeyWithoutPlaintextRequest GenerateDataKeyWithoutPlaintextRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextRequest dafnyValue) {
    GenerateDataKeyWithoutPlaintextRequest converted = new GenerateDataKeyWithoutPlaintextRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_EncryptionContext().is_Some()) {
      converted.withEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_KeySpec().is_Some()) {
      converted.withKeySpec(ToNative.DataKeySpec(dafnyValue.dtor_KeySpec().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      converted.withNumberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static GenerateRandomRequest GenerateRandomRequest(
      Dafny.Com.Amazonaws.Kms.Types.GenerateRandomRequest dafnyValue) {
    GenerateRandomRequest converted = new GenerateRandomRequest();
    if (dafnyValue.dtor_NumberOfBytes().is_Some()) {
      converted.withNumberOfBytes((dafnyValue.dtor_NumberOfBytes().dtor_value()));
    }
    if (dafnyValue.dtor_CustomKeyStoreId().is_Some()) {
      converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId().dtor_value()));
    }
    return converted;
  }

  public static GetKeyPolicyRequest GetKeyPolicyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyRequest dafnyValue) {
    GetKeyPolicyRequest converted = new GetKeyPolicyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withPolicyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    return converted;
  }

  public static GetKeyRotationStatusRequest GetKeyRotationStatusRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusRequest dafnyValue) {
    GetKeyRotationStatusRequest converted = new GetKeyRotationStatusRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    return converted;
  }

  public static GetParametersForImportRequest GetParametersForImportRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportRequest dafnyValue) {
    GetParametersForImportRequest converted = new GetParametersForImportRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withWrappingAlgorithm(ToNative.AlgorithmSpec(dafnyValue.dtor_WrappingAlgorithm()));
    converted.withWrappingKeySpec(ToNative.WrappingKeySpec(dafnyValue.dtor_WrappingKeySpec()));
    return converted;
  }

  public static GetPublicKeyRequest GetPublicKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyRequest dafnyValue) {
    GetPublicKeyRequest converted = new GetPublicKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static ImportKeyMaterialRequest ImportKeyMaterialRequest(
      Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialRequest dafnyValue) {
    ImportKeyMaterialRequest converted = new ImportKeyMaterialRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withImportToken(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_ImportToken()));
    converted.withEncryptedKeyMaterial(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_EncryptedKeyMaterial()));
    if (dafnyValue.dtor_ValidTo().is_Some()) {
      converted.withValidTo(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_ValidTo().dtor_value()));
    }
    if (dafnyValue.dtor_ExpirationModel().is_Some()) {
      converted.withExpirationModel(ToNative.ExpirationModelType(dafnyValue.dtor_ExpirationModel().dtor_value()));
    }
    return converted;
  }

  public static ListAliasesRequest ListAliasesRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListAliasesRequest dafnyValue) {
    ListAliasesRequest converted = new ListAliasesRequest();
    if (dafnyValue.dtor_KeyId().is_Some()) {
      converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.withLimit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      converted.withMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return converted;
  }

  public static ListGrantsRequest ListGrantsRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListGrantsRequest dafnyValue) {
    ListGrantsRequest converted = new ListGrantsRequest();
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.withLimit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      converted.withMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_GrantId().is_Some()) {
      converted.withGrantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    if (dafnyValue.dtor_GranteePrincipal().is_Some()) {
      converted.withGranteePrincipal(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GranteePrincipal().dtor_value()));
    }
    return converted;
  }

  public static ListKeyPoliciesRequest ListKeyPoliciesRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesRequest dafnyValue) {
    ListKeyPoliciesRequest converted = new ListKeyPoliciesRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.withLimit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      converted.withMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return converted;
  }

  public static ListResourceTagsRequest ListResourceTagsRequest(
      Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsRequest dafnyValue) {
    ListResourceTagsRequest converted = new ListResourceTagsRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.withLimit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Marker().is_Some()) {
      converted.withMarker(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Marker().dtor_value()));
    }
    return converted;
  }

  public static PutKeyPolicyRequest PutKeyPolicyRequest(
      Dafny.Com.Amazonaws.Kms.Types.PutKeyPolicyRequest dafnyValue) {
    PutKeyPolicyRequest converted = new PutKeyPolicyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withPolicyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName()));
    converted.withPolicy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy()));
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      converted.withBypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    return converted;
  }

  public static ReEncryptRequest ReEncryptRequest(
      Dafny.Com.Amazonaws.Kms.Types.ReEncryptRequest dafnyValue) {
    ReEncryptRequest converted = new ReEncryptRequest();
    converted.withCiphertextBlob(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_CiphertextBlob()));
    if (dafnyValue.dtor_SourceEncryptionContext().is_Some()) {
      converted.withSourceEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_SourceEncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_SourceKeyId().is_Some()) {
      converted.withSourceKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceKeyId().dtor_value()));
    }
    converted.withDestinationKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_DestinationKeyId()));
    if (dafnyValue.dtor_DestinationEncryptionContext().is_Some()) {
      converted.withDestinationEncryptionContext(ToNative.EncryptionContextType(dafnyValue.dtor_DestinationEncryptionContext().dtor_value()));
    }
    if (dafnyValue.dtor_SourceEncryptionAlgorithm().is_Some()) {
      converted.withSourceEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_SourceEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationEncryptionAlgorithm().is_Some()) {
      converted.withDestinationEncryptionAlgorithm(ToNative.EncryptionAlgorithmSpec(dafnyValue.dtor_DestinationEncryptionAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static ReplicateKeyRequest ReplicateKeyRequest(
      Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyRequest dafnyValue) {
    ReplicateKeyRequest converted = new ReplicateKeyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withReplicaRegion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaRegion()));
    if (dafnyValue.dtor_Policy().is_Some()) {
      converted.withPolicy(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Policy().dtor_value()));
    }
    if (dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().is_Some()) {
      converted.withBypassPolicyLockoutSafetyCheck((dafnyValue.dtor_BypassPolicyLockoutSafetyCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Description().is_Some()) {
      converted.withDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      converted.withTags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return converted;
  }

  public static RetireGrantRequest RetireGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.RetireGrantRequest dafnyValue) {
    RetireGrantRequest converted = new RetireGrantRequest();
    if (dafnyValue.dtor_GrantToken().is_Some()) {
      converted.withGrantToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantToken().dtor_value()));
    }
    if (dafnyValue.dtor_KeyId().is_Some()) {
      converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId().dtor_value()));
    }
    if (dafnyValue.dtor_GrantId().is_Some()) {
      converted.withGrantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId().dtor_value()));
    }
    return converted;
  }

  public static RevokeGrantRequest RevokeGrantRequest(
      Dafny.Com.Amazonaws.Kms.Types.RevokeGrantRequest dafnyValue) {
    RevokeGrantRequest converted = new RevokeGrantRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withGrantId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GrantId()));
    return converted;
  }

  public static ScheduleKeyDeletionRequest ScheduleKeyDeletionRequest(
      Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionRequest dafnyValue) {
    ScheduleKeyDeletionRequest converted = new ScheduleKeyDeletionRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    if (dafnyValue.dtor_PendingWindowInDays().is_Some()) {
      converted.withPendingWindowInDays((dafnyValue.dtor_PendingWindowInDays().dtor_value()));
    }
    return converted;
  }

  public static SignRequest SignRequest(Dafny.Com.Amazonaws.Kms.Types.SignRequest dafnyValue) {
    SignRequest converted = new SignRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withMessage(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_Message()));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      converted.withMessageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    converted.withSigningAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    return converted;
  }

  public static TagResourceRequest TagResourceRequest(
      Dafny.Com.Amazonaws.Kms.Types.TagResourceRequest dafnyValue) {
    TagResourceRequest converted = new TagResourceRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withTags(ToNative.TagList(dafnyValue.dtor_Tags()));
    return converted;
  }

  public static UntagResourceRequest UntagResourceRequest(
      Dafny.Com.Amazonaws.Kms.Types.UntagResourceRequest dafnyValue) {
    UntagResourceRequest converted = new UntagResourceRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withTagKeys(ToNative.TagKeyList(dafnyValue.dtor_TagKeys()));
    return converted;
  }

  public static UpdateAliasRequest UpdateAliasRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateAliasRequest dafnyValue) {
    UpdateAliasRequest converted = new UpdateAliasRequest();
    converted.withAliasName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AliasName()));
    converted.withTargetKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetKeyId()));
    return converted;
  }

  public static UpdateCustomKeyStoreRequest UpdateCustomKeyStoreRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreRequest dafnyValue) {
    UpdateCustomKeyStoreRequest converted = new UpdateCustomKeyStoreRequest();
    converted.withCustomKeyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CustomKeyStoreId()));
    if (dafnyValue.dtor_NewCustomKeyStoreName().is_Some()) {
      converted.withNewCustomKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NewCustomKeyStoreName().dtor_value()));
    }
    if (dafnyValue.dtor_KeyStorePassword().is_Some()) {
      converted.withKeyStorePassword(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyStorePassword().dtor_value()));
    }
    if (dafnyValue.dtor_CloudHsmClusterId().is_Some()) {
      converted.withCloudHsmClusterId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudHsmClusterId().dtor_value()));
    }
    return converted;
  }

  public static UpdateKeyDescriptionRequest UpdateKeyDescriptionRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdateKeyDescriptionRequest dafnyValue) {
    UpdateKeyDescriptionRequest converted = new UpdateKeyDescriptionRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Description()));
    return converted;
  }

  public static UpdatePrimaryRegionRequest UpdatePrimaryRegionRequest(
      Dafny.Com.Amazonaws.Kms.Types.UpdatePrimaryRegionRequest dafnyValue) {
    UpdatePrimaryRegionRequest converted = new UpdatePrimaryRegionRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withPrimaryRegion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PrimaryRegion()));
    return converted;
  }

  public static VerifyRequest VerifyRequest(
      Dafny.Com.Amazonaws.Kms.Types.VerifyRequest dafnyValue) {
    VerifyRequest converted = new VerifyRequest();
    converted.withKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyId()));
    converted.withMessage(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_Message()));
    if (dafnyValue.dtor_MessageType().is_Some()) {
      converted.withMessageType(ToNative.MessageType(dafnyValue.dtor_MessageType().dtor_value()));
    }
    converted.withSignature(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_Signature()));
    converted.withSigningAlgorithm(ToNative.SigningAlgorithmSpec(dafnyValue.dtor_SigningAlgorithm()));
    if (dafnyValue.dtor_GrantTokens().is_Some()) {
      converted.withGrantTokens(ToNative.GrantTokenList(dafnyValue.dtor_GrantTokens().dtor_value()));
    }
    return converted;
  }

  public static List<GrantOperation> GrantOperationList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.GrantOperation> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Kms.ToNative::GrantOperation);
  }

  public static GrantConstraints GrantConstraints(
      Dafny.Com.Amazonaws.Kms.Types.GrantConstraints dafnyValue) {
    GrantConstraints converted = new GrantConstraints();
    if (dafnyValue.dtor_EncryptionContextSubset().is_Some()) {
      converted.withEncryptionContextSubset(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextSubset().dtor_value()));
    }
    if (dafnyValue.dtor_EncryptionContextEquals().is_Some()) {
      converted.withEncryptionContextEquals(ToNative.EncryptionContextType(dafnyValue.dtor_EncryptionContextEquals().dtor_value()));
    }
    return converted;
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
      return CustomerMasterKeySpec.ECC_SECG_P256K1;
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
      return KeySpec.ECC_SECG_P256K1;
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
      return DataKeyPairSpec.ECC_SECG_P256K1;
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

  public static GrantOperation GrantOperation(
      Dafny.Com.Amazonaws.Kms.Types.GrantOperation dafnyValue) {
    if (dafnyValue.is_Decrypt()) {
      return GrantOperation.Decrypt;
    }
    if (dafnyValue.is_Encrypt()) {
      return GrantOperation.Encrypt;
    }
    if (dafnyValue.is_GenerateDataKey()) {
      return GrantOperation.GenerateDataKey;
    }
    if (dafnyValue.is_GenerateDataKeyWithoutPlaintext()) {
      return GrantOperation.GenerateDataKeyWithoutPlaintext;
    }
    if (dafnyValue.is_ReEncryptFrom()) {
      return GrantOperation.ReEncryptFrom;
    }
    if (dafnyValue.is_ReEncryptTo()) {
      return GrantOperation.ReEncryptTo;
    }
    if (dafnyValue.is_Sign()) {
      return GrantOperation.Sign;
    }
    if (dafnyValue.is_Verify()) {
      return GrantOperation.Verify;
    }
    if (dafnyValue.is_GetPublicKey()) {
      return GrantOperation.GetPublicKey;
    }
    if (dafnyValue.is_CreateGrant()) {
      return GrantOperation.CreateGrant;
    }
    if (dafnyValue.is_RetireGrant()) {
      return GrantOperation.RetireGrant;
    }
    if (dafnyValue.is_DescribeKey()) {
      return GrantOperation.DescribeKey;
    }
    if (dafnyValue.is_GenerateDataKeyPair()) {
      return GrantOperation.GenerateDataKeyPair;
    }
    if (dafnyValue.is_GenerateDataKeyPairWithoutPlaintext()) {
      return GrantOperation.GenerateDataKeyPairWithoutPlaintext;
    }
    return GrantOperation.fromValue(dafnyValue.toString());
  }

  public static Tag Tag(Dafny.Com.Amazonaws.Kms.Types.Tag dafnyValue) {
    Tag converted = new Tag();
    converted.withTagKey(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagKey()));
    converted.withTagValue(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TagValue()));
    return converted;
  }
}
