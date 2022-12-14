// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package Dafny.Com.Amazonaws.Kms;

import Dafny.Com.Amazonaws.Kms.Types.AliasListEntry;
import Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionResponse;
import Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.ConnectionErrorCodeType;
import Dafny.Com.Amazonaws.Kms.Types.ConnectionStateType;
import Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.CreateGrantResponse;
import Dafny.Com.Amazonaws.Kms.Types.CreateKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.CustomKeyStoresListEntry;
import Dafny.Com.Amazonaws.Kms.Types.CustomerMasterKeySpec;
import Dafny.Com.Amazonaws.Kms.Types.DataKeyPairSpec;
import Dafny.Com.Amazonaws.Kms.Types.DecryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresResponse;
import Dafny.Com.Amazonaws.Kms.Types.DescribeKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.EncryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec;
import Dafny.Com.Amazonaws.Kms.Types.Error;
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
import Dafny.Com.Amazonaws.Kms.Types.Error_Opaque;
import Dafny.Com.Amazonaws.Kms.Types.Error_TagException;
import Dafny.Com.Amazonaws.Kms.Types.Error_UnsupportedOperationException;
import Dafny.Com.Amazonaws.Kms.Types.ExpirationModelType;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateRandomResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.GrantConstraints;
import Dafny.Com.Amazonaws.Kms.Types.GrantListEntry;
import Dafny.Com.Amazonaws.Kms.Types.GrantOperation;
import Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialResponse;
import Dafny.Com.Amazonaws.Kms.Types.KeyManagerType;
import Dafny.Com.Amazonaws.Kms.Types.KeyMetadata;
import Dafny.Com.Amazonaws.Kms.Types.KeySpec;
import Dafny.Com.Amazonaws.Kms.Types.KeyState;
import Dafny.Com.Amazonaws.Kms.Types.KeyUsageType;
import Dafny.Com.Amazonaws.Kms.Types.ListAliasesResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListGrantsResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsResponse;
import Dafny.Com.Amazonaws.Kms.Types.MultiRegionConfiguration;
import Dafny.Com.Amazonaws.Kms.Types.MultiRegionKey;
import Dafny.Com.Amazonaws.Kms.Types.MultiRegionKeyType;
import Dafny.Com.Amazonaws.Kms.Types.OriginType;
import Dafny.Com.Amazonaws.Kms.Types.ReEncryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionResponse;
import Dafny.Com.Amazonaws.Kms.Types.SignResponse;
import Dafny.Com.Amazonaws.Kms.Types.SigningAlgorithmSpec;
import Dafny.Com.Amazonaws.Kms.Types.Tag;
import Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.VerifyResponse;
import Wrappers_Compile.Option;
import com.amazonaws.services.kms.model.AWSKMSException;
import com.amazonaws.services.kms.model.AlreadyExistsException;
import com.amazonaws.services.kms.model.CancelKeyDeletionResult;
import com.amazonaws.services.kms.model.CloudHsmClusterInUseException;
import com.amazonaws.services.kms.model.CloudHsmClusterInvalidConfigurationException;
import com.amazonaws.services.kms.model.CloudHsmClusterNotActiveException;
import com.amazonaws.services.kms.model.CloudHsmClusterNotFoundException;
import com.amazonaws.services.kms.model.CloudHsmClusterNotRelatedException;
import com.amazonaws.services.kms.model.ConnectCustomKeyStoreResult;
import com.amazonaws.services.kms.model.CreateCustomKeyStoreResult;
import com.amazonaws.services.kms.model.CreateGrantResult;
import com.amazonaws.services.kms.model.CreateKeyResult;
import com.amazonaws.services.kms.model.CustomKeyStoreHasCMKsException;
import com.amazonaws.services.kms.model.CustomKeyStoreInvalidStateException;
import com.amazonaws.services.kms.model.CustomKeyStoreNameInUseException;
import com.amazonaws.services.kms.model.CustomKeyStoreNotFoundException;
import com.amazonaws.services.kms.model.DecryptResult;
import com.amazonaws.services.kms.model.DeleteCustomKeyStoreResult;
import com.amazonaws.services.kms.model.DependencyTimeoutException;
import com.amazonaws.services.kms.model.DescribeCustomKeyStoresResult;
import com.amazonaws.services.kms.model.DescribeKeyResult;
import com.amazonaws.services.kms.model.DisabledException;
import com.amazonaws.services.kms.model.DisconnectCustomKeyStoreResult;
import com.amazonaws.services.kms.model.EncryptResult;
import com.amazonaws.services.kms.model.ExpiredImportTokenException;
import com.amazonaws.services.kms.model.GenerateDataKeyPairResult;
import com.amazonaws.services.kms.model.GenerateDataKeyPairWithoutPlaintextResult;
import com.amazonaws.services.kms.model.GenerateDataKeyResult;
import com.amazonaws.services.kms.model.GenerateDataKeyWithoutPlaintextResult;
import com.amazonaws.services.kms.model.GenerateRandomResult;
import com.amazonaws.services.kms.model.GetKeyPolicyResult;
import com.amazonaws.services.kms.model.GetKeyRotationStatusResult;
import com.amazonaws.services.kms.model.GetParametersForImportResult;
import com.amazonaws.services.kms.model.GetPublicKeyResult;
import com.amazonaws.services.kms.model.ImportKeyMaterialResult;
import com.amazonaws.services.kms.model.IncorrectKeyException;
import com.amazonaws.services.kms.model.IncorrectKeyMaterialException;
import com.amazonaws.services.kms.model.IncorrectTrustAnchorException;
import com.amazonaws.services.kms.model.InvalidAliasNameException;
import com.amazonaws.services.kms.model.InvalidArnException;
import com.amazonaws.services.kms.model.InvalidCiphertextException;
import com.amazonaws.services.kms.model.InvalidGrantIdException;
import com.amazonaws.services.kms.model.InvalidGrantTokenException;
import com.amazonaws.services.kms.model.InvalidImportTokenException;
import com.amazonaws.services.kms.model.InvalidKeyUsageException;
import com.amazonaws.services.kms.model.InvalidMarkerException;
import com.amazonaws.services.kms.model.KMSInternalException;
import com.amazonaws.services.kms.model.KMSInvalidSignatureException;
import com.amazonaws.services.kms.model.KMSInvalidStateException;
import com.amazonaws.services.kms.model.KeyUnavailableException;
import com.amazonaws.services.kms.model.LimitExceededException;
import com.amazonaws.services.kms.model.ListAliasesResult;
import com.amazonaws.services.kms.model.ListGrantsResult;
import com.amazonaws.services.kms.model.ListKeyPoliciesResult;
import com.amazonaws.services.kms.model.ListResourceTagsResult;
import com.amazonaws.services.kms.model.MalformedPolicyDocumentException;
import com.amazonaws.services.kms.model.NotFoundException;
import com.amazonaws.services.kms.model.ReEncryptResult;
import com.amazonaws.services.kms.model.ReplicateKeyResult;
import com.amazonaws.services.kms.model.ScheduleKeyDeletionResult;
import com.amazonaws.services.kms.model.SignResult;
import com.amazonaws.services.kms.model.TagException;
import com.amazonaws.services.kms.model.UnsupportedOperationException;
import com.amazonaws.services.kms.model.UpdateCustomKeyStoreResult;
import com.amazonaws.services.kms.model.VerifyResult;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Boolean;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Integer;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class ToDafny {
  public static CancelKeyDeletionResponse CancelKeyDeletionResponse(
      CancelKeyDeletionResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    return new CancelKeyDeletionResponse(keyId);
  }

  public static ConnectCustomKeyStoreResponse ConnectCustomKeyStoreResponse(
      ConnectCustomKeyStoreResult nativeValue) {
    return new ConnectCustomKeyStoreResponse();
  }

  public static CreateCustomKeyStoreResponse CreateCustomKeyStoreResponse(
      CreateCustomKeyStoreResult nativeValue) {
    Option<DafnySequence<? extends Character>> customKeyStoreId;
    customKeyStoreId = Objects.nonNull(nativeValue.getCustomKeyStoreId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCustomKeyStoreId()))
        : Option.create_None();
    return new CreateCustomKeyStoreResponse(customKeyStoreId);
  }

  public static CreateGrantResponse CreateGrantResponse(CreateGrantResult nativeValue) {
    Option<DafnySequence<? extends Character>> grantToken;
    grantToken = Objects.nonNull(nativeValue.getGrantToken()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getGrantToken()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> grantId;
    grantId = Objects.nonNull(nativeValue.getGrantId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getGrantId()))
        : Option.create_None();
    return new CreateGrantResponse(grantToken, grantId);
  }

  public static CreateKeyResponse CreateKeyResponse(CreateKeyResult nativeValue) {
    Option<KeyMetadata> keyMetadata;
    keyMetadata = Objects.nonNull(nativeValue.getKeyMetadata()) ?
        Option.create_Some(ToDafny.KeyMetadata(nativeValue.getKeyMetadata()))
        : Option.create_None();
    return new CreateKeyResponse(keyMetadata);
  }

  public static DecryptResponse DecryptResponse(DecryptResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> plaintext;
    plaintext = Objects.nonNull(nativeValue.getPlaintext()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPlaintext()))
        : Option.create_None();
    Option<EncryptionAlgorithmSpec> encryptionAlgorithm;
    encryptionAlgorithm = Objects.nonNull(nativeValue.getEncryptionAlgorithm()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpec(nativeValue.getEncryptionAlgorithm()))
        : Option.create_None();
    return new DecryptResponse(keyId, plaintext, encryptionAlgorithm);
  }

  public static DeleteCustomKeyStoreResponse DeleteCustomKeyStoreResponse(
      DeleteCustomKeyStoreResult nativeValue) {
    return new DeleteCustomKeyStoreResponse();
  }

  public static DescribeCustomKeyStoresResponse DescribeCustomKeyStoresResponse(
      DescribeCustomKeyStoresResult nativeValue) {
    Option<DafnySequence<? extends CustomKeyStoresListEntry>> customKeyStores;
    customKeyStores = Objects.nonNull(nativeValue.getCustomKeyStores()) ?
        Option.create_Some(ToDafny.CustomKeyStoresList(nativeValue.getCustomKeyStores()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nextMarker;
    nextMarker = Objects.nonNull(nativeValue.getNextMarker()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getNextMarker()))
        : Option.create_None();
    Option<Boolean> truncated;
    truncated = Objects.nonNull(nativeValue.getTruncated()) ?
        Option.create_Some((nativeValue.getTruncated()))
        : Option.create_None();
    return new DescribeCustomKeyStoresResponse(customKeyStores, nextMarker, truncated);
  }

  public static DescribeKeyResponse DescribeKeyResponse(DescribeKeyResult nativeValue) {
    Option<KeyMetadata> keyMetadata;
    keyMetadata = Objects.nonNull(nativeValue.getKeyMetadata()) ?
        Option.create_Some(ToDafny.KeyMetadata(nativeValue.getKeyMetadata()))
        : Option.create_None();
    return new DescribeKeyResponse(keyMetadata);
  }

  public static DisconnectCustomKeyStoreResponse DisconnectCustomKeyStoreResponse(
      DisconnectCustomKeyStoreResult nativeValue) {
    return new DisconnectCustomKeyStoreResponse();
  }

  public static EncryptResponse EncryptResponse(EncryptResult nativeValue) {
    Option<DafnySequence<? extends Byte>> ciphertextBlob;
    ciphertextBlob = Objects.nonNull(nativeValue.getCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<EncryptionAlgorithmSpec> encryptionAlgorithm;
    encryptionAlgorithm = Objects.nonNull(nativeValue.getEncryptionAlgorithm()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpec(nativeValue.getEncryptionAlgorithm()))
        : Option.create_None();
    return new EncryptResponse(ciphertextBlob, keyId, encryptionAlgorithm);
  }

  public static GenerateDataKeyResponse GenerateDataKeyResponse(GenerateDataKeyResult nativeValue) {
    Option<DafnySequence<? extends Byte>> ciphertextBlob;
    ciphertextBlob = Objects.nonNull(nativeValue.getCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> plaintext;
    plaintext = Objects.nonNull(nativeValue.getPlaintext()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPlaintext()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    return new GenerateDataKeyResponse(ciphertextBlob, plaintext, keyId);
  }

  public static GenerateDataKeyPairResponse GenerateDataKeyPairResponse(
      GenerateDataKeyPairResult nativeValue) {
    Option<DafnySequence<? extends Byte>> privateKeyCiphertextBlob;
    privateKeyCiphertextBlob = Objects.nonNull(nativeValue.getPrivateKeyCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPrivateKeyCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> privateKeyPlaintext;
    privateKeyPlaintext = Objects.nonNull(nativeValue.getPrivateKeyPlaintext()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPrivateKeyPlaintext()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.getPublicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPublicKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DataKeyPairSpec> keyPairSpec;
    keyPairSpec = Objects.nonNull(nativeValue.getKeyPairSpec()) ?
        Option.create_Some(ToDafny.DataKeyPairSpec(nativeValue.getKeyPairSpec()))
        : Option.create_None();
    return new GenerateDataKeyPairResponse(privateKeyCiphertextBlob, privateKeyPlaintext, publicKey, keyId, keyPairSpec);
  }

  public static GenerateDataKeyPairWithoutPlaintextResponse GenerateDataKeyPairWithoutPlaintextResponse(
      GenerateDataKeyPairWithoutPlaintextResult nativeValue) {
    Option<DafnySequence<? extends Byte>> privateKeyCiphertextBlob;
    privateKeyCiphertextBlob = Objects.nonNull(nativeValue.getPrivateKeyCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPrivateKeyCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.getPublicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPublicKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DataKeyPairSpec> keyPairSpec;
    keyPairSpec = Objects.nonNull(nativeValue.getKeyPairSpec()) ?
        Option.create_Some(ToDafny.DataKeyPairSpec(nativeValue.getKeyPairSpec()))
        : Option.create_None();
    return new GenerateDataKeyPairWithoutPlaintextResponse(privateKeyCiphertextBlob, publicKey, keyId, keyPairSpec);
  }

  public static GenerateDataKeyWithoutPlaintextResponse GenerateDataKeyWithoutPlaintextResponse(
      GenerateDataKeyWithoutPlaintextResult nativeValue) {
    Option<DafnySequence<? extends Byte>> ciphertextBlob;
    ciphertextBlob = Objects.nonNull(nativeValue.getCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    return new GenerateDataKeyWithoutPlaintextResponse(ciphertextBlob, keyId);
  }

  public static GenerateRandomResponse GenerateRandomResponse(GenerateRandomResult nativeValue) {
    Option<DafnySequence<? extends Byte>> plaintext;
    plaintext = Objects.nonNull(nativeValue.getPlaintext()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPlaintext()))
        : Option.create_None();
    return new GenerateRandomResponse(plaintext);
  }

  public static GetKeyPolicyResponse GetKeyPolicyResponse(GetKeyPolicyResult nativeValue) {
    Option<DafnySequence<? extends Character>> policy;
    policy = Objects.nonNull(nativeValue.getPolicy()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getPolicy()))
        : Option.create_None();
    return new GetKeyPolicyResponse(policy);
  }

  public static GetKeyRotationStatusResponse GetKeyRotationStatusResponse(
      GetKeyRotationStatusResult nativeValue) {
    Option<Boolean> keyRotationEnabled;
    keyRotationEnabled = Objects.nonNull(nativeValue.getKeyRotationEnabled()) ?
        Option.create_Some((nativeValue.getKeyRotationEnabled()))
        : Option.create_None();
    return new GetKeyRotationStatusResponse(keyRotationEnabled);
  }

  public static GetParametersForImportResponse GetParametersForImportResponse(
      GetParametersForImportResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> importToken;
    importToken = Objects.nonNull(nativeValue.getImportToken()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getImportToken()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.getPublicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPublicKey()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> parametersValidTo;
    parametersValidTo = Objects.nonNull(nativeValue.getParametersValidTo()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getParametersValidTo()))
        : Option.create_None();
    return new GetParametersForImportResponse(keyId, importToken, publicKey, parametersValidTo);
  }

  public static GetPublicKeyResponse GetPublicKeyResponse(GetPublicKeyResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> publicKey;
    publicKey = Objects.nonNull(nativeValue.getPublicKey()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getPublicKey()))
        : Option.create_None();
    Option<CustomerMasterKeySpec> customerMasterKeySpec;
    customerMasterKeySpec = Objects.nonNull(nativeValue.getCustomerMasterKeySpec()) ?
        Option.create_Some(ToDafny.CustomerMasterKeySpec(nativeValue.getCustomerMasterKeySpec()))
        : Option.create_None();
    Option<KeySpec> keySpec;
    keySpec = Objects.nonNull(nativeValue.getKeySpec()) ?
        Option.create_Some(ToDafny.KeySpec(nativeValue.getKeySpec()))
        : Option.create_None();
    Option<KeyUsageType> keyUsage;
    keyUsage = Objects.nonNull(nativeValue.getKeyUsage()) ?
        Option.create_Some(ToDafny.KeyUsageType(nativeValue.getKeyUsage()))
        : Option.create_None();
    Option<DafnySequence<? extends EncryptionAlgorithmSpec>> encryptionAlgorithms;
    encryptionAlgorithms = Objects.nonNull(nativeValue.getEncryptionAlgorithms()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpecList(nativeValue.getEncryptionAlgorithms()))
        : Option.create_None();
    Option<DafnySequence<? extends SigningAlgorithmSpec>> signingAlgorithms;
    signingAlgorithms = Objects.nonNull(nativeValue.getSigningAlgorithms()) ?
        Option.create_Some(ToDafny.SigningAlgorithmSpecList(nativeValue.getSigningAlgorithms()))
        : Option.create_None();
    return new GetPublicKeyResponse(keyId, publicKey, customerMasterKeySpec, keySpec, keyUsage, encryptionAlgorithms, signingAlgorithms);
  }

  public static ImportKeyMaterialResponse ImportKeyMaterialResponse(
      ImportKeyMaterialResult nativeValue) {
    return new ImportKeyMaterialResponse();
  }

  public static ListAliasesResponse ListAliasesResponse(ListAliasesResult nativeValue) {
    Option<DafnySequence<? extends AliasListEntry>> aliases;
    aliases = Objects.nonNull(nativeValue.getAliases()) ?
        Option.create_Some(ToDafny.AliasList(nativeValue.getAliases()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nextMarker;
    nextMarker = Objects.nonNull(nativeValue.getNextMarker()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getNextMarker()))
        : Option.create_None();
    Option<Boolean> truncated;
    truncated = Objects.nonNull(nativeValue.getTruncated()) ?
        Option.create_Some((nativeValue.getTruncated()))
        : Option.create_None();
    return new ListAliasesResponse(aliases, nextMarker, truncated);
  }

  public static ListGrantsResponse ListGrantsResponse(ListGrantsResult nativeValue) {
    Option<DafnySequence<? extends GrantListEntry>> grants;
    grants = Objects.nonNull(nativeValue.getGrants()) ?
        Option.create_Some(ToDafny.GrantList(nativeValue.getGrants()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nextMarker;
    nextMarker = Objects.nonNull(nativeValue.getNextMarker()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getNextMarker()))
        : Option.create_None();
    Option<Boolean> truncated;
    truncated = Objects.nonNull(nativeValue.getTruncated()) ?
        Option.create_Some((nativeValue.getTruncated()))
        : Option.create_None();
    return new ListGrantsResponse(grants, nextMarker, truncated);
  }

  public static ListKeyPoliciesResponse ListKeyPoliciesResponse(ListKeyPoliciesResult nativeValue) {
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> policyNames;
    policyNames = Objects.nonNull(nativeValue.getPolicyNames()) ?
        Option.create_Some(ToDafny.PolicyNameList(nativeValue.getPolicyNames()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nextMarker;
    nextMarker = Objects.nonNull(nativeValue.getNextMarker()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getNextMarker()))
        : Option.create_None();
    Option<Boolean> truncated;
    truncated = Objects.nonNull(nativeValue.getTruncated()) ?
        Option.create_Some((nativeValue.getTruncated()))
        : Option.create_None();
    return new ListKeyPoliciesResponse(policyNames, nextMarker, truncated);
  }

  public static ListResourceTagsResponse ListResourceTagsResponse(
      ListResourceTagsResult nativeValue) {
    Option<DafnySequence<? extends Tag>> tags;
    tags = Objects.nonNull(nativeValue.getTags()) ?
        Option.create_Some(ToDafny.TagList(nativeValue.getTags()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nextMarker;
    nextMarker = Objects.nonNull(nativeValue.getNextMarker()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getNextMarker()))
        : Option.create_None();
    Option<Boolean> truncated;
    truncated = Objects.nonNull(nativeValue.getTruncated()) ?
        Option.create_Some((nativeValue.getTruncated()))
        : Option.create_None();
    return new ListResourceTagsResponse(tags, nextMarker, truncated);
  }

  public static ReEncryptResponse ReEncryptResponse(ReEncryptResult nativeValue) {
    Option<DafnySequence<? extends Byte>> ciphertextBlob;
    ciphertextBlob = Objects.nonNull(nativeValue.getCiphertextBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getCiphertextBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> sourceKeyId;
    sourceKeyId = Objects.nonNull(nativeValue.getSourceKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getSourceKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<EncryptionAlgorithmSpec> sourceEncryptionAlgorithm;
    sourceEncryptionAlgorithm = Objects.nonNull(nativeValue.getSourceEncryptionAlgorithm()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpec(nativeValue.getSourceEncryptionAlgorithm()))
        : Option.create_None();
    Option<EncryptionAlgorithmSpec> destinationEncryptionAlgorithm;
    destinationEncryptionAlgorithm = Objects.nonNull(nativeValue.getDestinationEncryptionAlgorithm()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpec(nativeValue.getDestinationEncryptionAlgorithm()))
        : Option.create_None();
    return new ReEncryptResponse(ciphertextBlob, sourceKeyId, keyId, sourceEncryptionAlgorithm, destinationEncryptionAlgorithm);
  }

  public static ReplicateKeyResponse ReplicateKeyResponse(ReplicateKeyResult nativeValue) {
    Option<KeyMetadata> replicaKeyMetadata;
    replicaKeyMetadata = Objects.nonNull(nativeValue.getReplicaKeyMetadata()) ?
        Option.create_Some(ToDafny.KeyMetadata(nativeValue.getReplicaKeyMetadata()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> replicaPolicy;
    replicaPolicy = Objects.nonNull(nativeValue.getReplicaPolicy()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getReplicaPolicy()))
        : Option.create_None();
    Option<DafnySequence<? extends Tag>> replicaTags;
    replicaTags = Objects.nonNull(nativeValue.getReplicaTags()) ?
        Option.create_Some(ToDafny.TagList(nativeValue.getReplicaTags()))
        : Option.create_None();
    return new ReplicateKeyResponse(replicaKeyMetadata, replicaPolicy, replicaTags);
  }

  public static ScheduleKeyDeletionResponse ScheduleKeyDeletionResponse(
      ScheduleKeyDeletionResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> deletionDate;
    deletionDate = Objects.nonNull(nativeValue.getDeletionDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getDeletionDate()))
        : Option.create_None();
    Option<KeyState> keyState;
    keyState = Objects.nonNull(nativeValue.getKeyState()) ?
        Option.create_Some(ToDafny.KeyState(nativeValue.getKeyState()))
        : Option.create_None();
    Option<Integer> pendingWindowInDays;
    pendingWindowInDays = Objects.nonNull(nativeValue.getPendingWindowInDays()) ?
        Option.create_Some((nativeValue.getPendingWindowInDays()))
        : Option.create_None();
    return new ScheduleKeyDeletionResponse(keyId, deletionDate, keyState, pendingWindowInDays);
  }

  public static SignResponse SignResponse(SignResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> signature;
    signature = Objects.nonNull(nativeValue.getSignature()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.getSignature()))
        : Option.create_None();
    Option<SigningAlgorithmSpec> signingAlgorithm;
    signingAlgorithm = Objects.nonNull(nativeValue.getSigningAlgorithm()) ?
        Option.create_Some(ToDafny.SigningAlgorithmSpec(nativeValue.getSigningAlgorithm()))
        : Option.create_None();
    return new SignResponse(keyId, signature, signingAlgorithm);
  }

  public static UpdateCustomKeyStoreResponse UpdateCustomKeyStoreResponse(
      UpdateCustomKeyStoreResult nativeValue) {
    return new UpdateCustomKeyStoreResponse();
  }

  public static VerifyResponse VerifyResponse(VerifyResult nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<Boolean> signatureValid;
    signatureValid = Objects.nonNull(nativeValue.getSignatureValid()) ?
        Option.create_Some((nativeValue.getSignatureValid()))
        : Option.create_None();
    Option<SigningAlgorithmSpec> signingAlgorithm;
    signingAlgorithm = Objects.nonNull(nativeValue.getSigningAlgorithm()) ?
        Option.create_Some(ToDafny.SigningAlgorithmSpec(nativeValue.getSigningAlgorithm()))
        : Option.create_None();
    return new VerifyResponse(keyId, signatureValid, signingAlgorithm);
  }

  public static KeyMetadata KeyMetadata(com.amazonaws.services.kms.model.KeyMetadata nativeValue) {
    Option<DafnySequence<? extends Character>> aWSAccountId;
    aWSAccountId = Objects.nonNull(nativeValue.getAWSAccountId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getAWSAccountId()))
        : Option.create_None();
    DafnySequence<? extends Character> keyId;
    keyId = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId());
    Option<DafnySequence<? extends Character>> arn;
    arn = Objects.nonNull(nativeValue.getArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getArn()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> creationDate;
    creationDate = Objects.nonNull(nativeValue.getCreationDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCreationDate()))
        : Option.create_None();
    Option<Boolean> enabled;
    enabled = Objects.nonNull(nativeValue.getEnabled()) ?
        Option.create_Some((nativeValue.getEnabled()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> description;
    description = Objects.nonNull(nativeValue.getDescription()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getDescription()))
        : Option.create_None();
    Option<KeyUsageType> keyUsage;
    keyUsage = Objects.nonNull(nativeValue.getKeyUsage()) ?
        Option.create_Some(ToDafny.KeyUsageType(nativeValue.getKeyUsage()))
        : Option.create_None();
    Option<KeyState> keyState;
    keyState = Objects.nonNull(nativeValue.getKeyState()) ?
        Option.create_Some(ToDafny.KeyState(nativeValue.getKeyState()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> deletionDate;
    deletionDate = Objects.nonNull(nativeValue.getDeletionDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getDeletionDate()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> validTo;
    validTo = Objects.nonNull(nativeValue.getValidTo()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getValidTo()))
        : Option.create_None();
    Option<OriginType> origin;
    origin = Objects.nonNull(nativeValue.getOrigin()) ?
        Option.create_Some(ToDafny.OriginType(nativeValue.getOrigin()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> customKeyStoreId;
    customKeyStoreId = Objects.nonNull(nativeValue.getCustomKeyStoreId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCustomKeyStoreId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> cloudHsmClusterId;
    cloudHsmClusterId = Objects.nonNull(nativeValue.getCloudHsmClusterId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCloudHsmClusterId()))
        : Option.create_None();
    Option<ExpirationModelType> expirationModel;
    expirationModel = Objects.nonNull(nativeValue.getExpirationModel()) ?
        Option.create_Some(ToDafny.ExpirationModelType(nativeValue.getExpirationModel()))
        : Option.create_None();
    Option<KeyManagerType> keyManager;
    keyManager = Objects.nonNull(nativeValue.getKeyManager()) ?
        Option.create_Some(ToDafny.KeyManagerType(nativeValue.getKeyManager()))
        : Option.create_None();
    Option<CustomerMasterKeySpec> customerMasterKeySpec;
    customerMasterKeySpec = Objects.nonNull(nativeValue.getCustomerMasterKeySpec()) ?
        Option.create_Some(ToDafny.CustomerMasterKeySpec(nativeValue.getCustomerMasterKeySpec()))
        : Option.create_None();
    Option<KeySpec> keySpec;
    keySpec = Objects.nonNull(nativeValue.getKeySpec()) ?
        Option.create_Some(ToDafny.KeySpec(nativeValue.getKeySpec()))
        : Option.create_None();
    Option<DafnySequence<? extends EncryptionAlgorithmSpec>> encryptionAlgorithms;
    encryptionAlgorithms = Objects.nonNull(nativeValue.getEncryptionAlgorithms()) ?
        Option.create_Some(ToDafny.EncryptionAlgorithmSpecList(nativeValue.getEncryptionAlgorithms()))
        : Option.create_None();
    Option<DafnySequence<? extends SigningAlgorithmSpec>> signingAlgorithms;
    signingAlgorithms = Objects.nonNull(nativeValue.getSigningAlgorithms()) ?
        Option.create_Some(ToDafny.SigningAlgorithmSpecList(nativeValue.getSigningAlgorithms()))
        : Option.create_None();
    Option<Boolean> multiRegion;
    multiRegion = Objects.nonNull(nativeValue.getMultiRegion()) ?
        Option.create_Some((nativeValue.getMultiRegion()))
        : Option.create_None();
    Option<MultiRegionConfiguration> multiRegionConfiguration;
    multiRegionConfiguration = Objects.nonNull(nativeValue.getMultiRegionConfiguration()) ?
        Option.create_Some(ToDafny.MultiRegionConfiguration(nativeValue.getMultiRegionConfiguration()))
        : Option.create_None();
    Option<Integer> pendingDeletionWindowInDays;
    pendingDeletionWindowInDays = Objects.nonNull(nativeValue.getPendingDeletionWindowInDays()) ?
        Option.create_Some((nativeValue.getPendingDeletionWindowInDays()))
        : Option.create_None();
    return new KeyMetadata(aWSAccountId, keyId, arn, creationDate, enabled, description, keyUsage, keyState, deletionDate, validTo, origin, customKeyStoreId, cloudHsmClusterId, expirationModel, keyManager, customerMasterKeySpec, keySpec, encryptionAlgorithms, signingAlgorithms, multiRegion, multiRegionConfiguration, pendingDeletionWindowInDays);
  }

  public static DafnySequence<? extends CustomKeyStoresListEntry> CustomKeyStoresList(
      List<com.amazonaws.services.kms.model.CustomKeyStoresListEntry> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::CustomKeyStoresListEntry, 
        CustomKeyStoresListEntry._typeDescriptor());
  }

  public static DafnySequence<? extends EncryptionAlgorithmSpec> EncryptionAlgorithmSpecList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::EncryptionAlgorithmSpec, 
        EncryptionAlgorithmSpec._typeDescriptor());
  }

  public static DafnySequence<? extends SigningAlgorithmSpec> SigningAlgorithmSpecList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::SigningAlgorithmSpec, 
        SigningAlgorithmSpec._typeDescriptor());
  }

  public static DafnySequence<? extends AliasListEntry> AliasList(
      List<com.amazonaws.services.kms.model.AliasListEntry> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::AliasListEntry, 
        AliasListEntry._typeDescriptor());
  }

  public static DafnySequence<? extends GrantListEntry> GrantList(
      List<com.amazonaws.services.kms.model.GrantListEntry> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::GrantListEntry, 
        GrantListEntry._typeDescriptor());
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> PolicyNameList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends Tag> TagList(
      List<com.amazonaws.services.kms.model.Tag> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::Tag, 
        Tag._typeDescriptor());
  }

  public static MultiRegionConfiguration MultiRegionConfiguration(
      com.amazonaws.services.kms.model.MultiRegionConfiguration nativeValue) {
    Option<MultiRegionKeyType> multiRegionKeyType;
    multiRegionKeyType = Objects.nonNull(nativeValue.getMultiRegionKeyType()) ?
        Option.create_Some(ToDafny.MultiRegionKeyType(nativeValue.getMultiRegionKeyType()))
        : Option.create_None();
    Option<MultiRegionKey> primaryKey;
    primaryKey = Objects.nonNull(nativeValue.getPrimaryKey()) ?
        Option.create_Some(ToDafny.MultiRegionKey(nativeValue.getPrimaryKey()))
        : Option.create_None();
    Option<DafnySequence<? extends MultiRegionKey>> replicaKeys;
    replicaKeys = Objects.nonNull(nativeValue.getReplicaKeys()) ?
        Option.create_Some(ToDafny.MultiRegionKeyList(nativeValue.getReplicaKeys()))
        : Option.create_None();
    return new MultiRegionConfiguration(multiRegionKeyType, primaryKey, replicaKeys);
  }

  public static CustomKeyStoresListEntry CustomKeyStoresListEntry(
      com.amazonaws.services.kms.model.CustomKeyStoresListEntry nativeValue) {
    Option<DafnySequence<? extends Character>> customKeyStoreId;
    customKeyStoreId = Objects.nonNull(nativeValue.getCustomKeyStoreId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCustomKeyStoreId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> customKeyStoreName;
    customKeyStoreName = Objects.nonNull(nativeValue.getCustomKeyStoreName()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCustomKeyStoreName()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> cloudHsmClusterId;
    cloudHsmClusterId = Objects.nonNull(nativeValue.getCloudHsmClusterId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCloudHsmClusterId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> trustAnchorCertificate;
    trustAnchorCertificate = Objects.nonNull(nativeValue.getTrustAnchorCertificate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getTrustAnchorCertificate()))
        : Option.create_None();
    Option<ConnectionStateType> connectionState;
    connectionState = Objects.nonNull(nativeValue.getConnectionState()) ?
        Option.create_Some(ToDafny.ConnectionStateType(nativeValue.getConnectionState()))
        : Option.create_None();
    Option<ConnectionErrorCodeType> connectionErrorCode;
    connectionErrorCode = Objects.nonNull(nativeValue.getConnectionErrorCode()) ?
        Option.create_Some(ToDafny.ConnectionErrorCodeType(nativeValue.getConnectionErrorCode()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> creationDate;
    creationDate = Objects.nonNull(nativeValue.getCreationDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCreationDate()))
        : Option.create_None();
    return new CustomKeyStoresListEntry(customKeyStoreId, customKeyStoreName, cloudHsmClusterId, trustAnchorCertificate, connectionState, connectionErrorCode, creationDate);
  }

  public static AliasListEntry AliasListEntry(
      com.amazonaws.services.kms.model.AliasListEntry nativeValue) {
    Option<DafnySequence<? extends Character>> aliasName;
    aliasName = Objects.nonNull(nativeValue.getAliasName()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getAliasName()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> aliasArn;
    aliasArn = Objects.nonNull(nativeValue.getAliasArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getAliasArn()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> targetKeyId;
    targetKeyId = Objects.nonNull(nativeValue.getTargetKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getTargetKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> creationDate;
    creationDate = Objects.nonNull(nativeValue.getCreationDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCreationDate()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> lastUpdatedDate;
    lastUpdatedDate = Objects.nonNull(nativeValue.getLastUpdatedDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getLastUpdatedDate()))
        : Option.create_None();
    return new AliasListEntry(aliasName, aliasArn, targetKeyId, creationDate, lastUpdatedDate);
  }

  public static GrantListEntry GrantListEntry(
      com.amazonaws.services.kms.model.GrantListEntry nativeValue) {
    Option<DafnySequence<? extends Character>> keyId;
    keyId = Objects.nonNull(nativeValue.getKeyId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getKeyId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> grantId;
    grantId = Objects.nonNull(nativeValue.getGrantId()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getGrantId()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> name;
    name = Objects.nonNull(nativeValue.getName()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getName()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> creationDate;
    creationDate = Objects.nonNull(nativeValue.getCreationDate()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getCreationDate()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> granteePrincipal;
    granteePrincipal = Objects.nonNull(nativeValue.getGranteePrincipal()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getGranteePrincipal()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> retiringPrincipal;
    retiringPrincipal = Objects.nonNull(nativeValue.getRetiringPrincipal()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getRetiringPrincipal()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> issuingAccount;
    issuingAccount = Objects.nonNull(nativeValue.getIssuingAccount()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getIssuingAccount()))
        : Option.create_None();
    Option<DafnySequence<? extends GrantOperation>> operations;
    operations = Objects.nonNull(nativeValue.getOperations()) ?
        Option.create_Some(ToDafny.GrantOperationList(nativeValue.getOperations()))
        : Option.create_None();
    Option<GrantConstraints> constraints;
    constraints = Objects.nonNull(nativeValue.getConstraints()) ?
        Option.create_Some(ToDafny.GrantConstraints(nativeValue.getConstraints()))
        : Option.create_None();
    return new GrantListEntry(keyId, grantId, name, creationDate, granteePrincipal, retiringPrincipal, issuingAccount, operations, constraints);
  }

  public static Tag Tag(com.amazonaws.services.kms.model.Tag nativeValue) {
    DafnySequence<? extends Character> tagKey;
    tagKey = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getTagKey());
    DafnySequence<? extends Character> tagValue;
    tagValue = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getTagValue());
    return new Tag(tagKey, tagValue);
  }

  public static MultiRegionKey MultiRegionKey(
      com.amazonaws.services.kms.model.MultiRegionKey nativeValue) {
    Option<DafnySequence<? extends Character>> arn;
    arn = Objects.nonNull(nativeValue.getArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getArn()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> region;
    region = Objects.nonNull(nativeValue.getRegion()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getRegion()))
        : Option.create_None();
    return new MultiRegionKey(arn, region);
  }

  public static DafnySequence<? extends MultiRegionKey> MultiRegionKeyList(
      List<com.amazonaws.services.kms.model.MultiRegionKey> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::MultiRegionKey, 
        MultiRegionKey._typeDescriptor());
  }

  public static DafnySequence<? extends GrantOperation> GrantOperationList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        Dafny.Com.Amazonaws.Kms.ToDafny::GrantOperation, 
        GrantOperation._typeDescriptor());
  }

  public static GrantConstraints GrantConstraints(
      com.amazonaws.services.kms.model.GrantConstraints nativeValue) {
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> encryptionContextSubset;
    encryptionContextSubset = Objects.nonNull(nativeValue.getEncryptionContextSubset()) ?
        Option.create_Some(ToDafny.EncryptionContextType(nativeValue.getEncryptionContextSubset()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> encryptionContextEquals;
    encryptionContextEquals = Objects.nonNull(nativeValue.getEncryptionContextEquals()) ?
        Option.create_Some(ToDafny.EncryptionContextType(nativeValue.getEncryptionContextEquals()))
        : Option.create_None();
    return new GrantConstraints(encryptionContextSubset, encryptionContextEquals);
  }

  public static DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> EncryptionContextType(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence);
  }

  public static Error Error(CustomKeyStoreHasCMKsException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CustomKeyStoreHasCMKsException(message);
  }

  public static Error Error(CloudHsmClusterNotFoundException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CloudHsmClusterNotFoundException(message);
  }

  public static Error Error(InvalidImportTokenException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidImportTokenException(message);
  }

  public static Error Error(TagException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_TagException(message);
  }

  public static Error Error(MalformedPolicyDocumentException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_MalformedPolicyDocumentException(message);
  }

  public static Error Error(InvalidMarkerException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidMarkerException(message);
  }

  public static Error Error(InvalidGrantIdException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidGrantIdException(message);
  }

  public static Error Error(IncorrectKeyException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_IncorrectKeyException(message);
  }

  public static Error Error(CloudHsmClusterNotActiveException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CloudHsmClusterNotActiveException(message);
  }

  public static Error Error(InvalidGrantTokenException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidGrantTokenException(message);
  }

  public static Error Error(ExpiredImportTokenException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_ExpiredImportTokenException(message);
  }

  public static Error Error(KMSInvalidStateException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_KMSInvalidStateException(message);
  }

  public static Error Error(KeyUnavailableException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_KeyUnavailableException(message);
  }

  public static Error Error(CustomKeyStoreNameInUseException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CustomKeyStoreNameInUseException(message);
  }

  public static Error Error(DependencyTimeoutException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_DependencyTimeoutException(message);
  }

  public static Error Error(UnsupportedOperationException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_UnsupportedOperationException(message);
  }

  public static Error Error(CustomKeyStoreInvalidStateException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CustomKeyStoreInvalidStateException(message);
  }

  public static Error Error(CloudHsmClusterNotRelatedException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CloudHsmClusterNotRelatedException(message);
  }

  public static Error Error(DisabledException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_DisabledException(message);
  }

  public static Error Error(InvalidAliasNameException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidAliasNameException(message);
  }

  public static Error Error(InvalidKeyUsageException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidKeyUsageException(message);
  }

  public static Error Error(CustomKeyStoreNotFoundException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CustomKeyStoreNotFoundException(message);
  }

  public static Error Error(AlreadyExistsException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_AlreadyExistsException(message);
  }

  public static Error Error(InvalidArnException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidArnException(message);
  }

  public static Error Error(CloudHsmClusterInUseException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CloudHsmClusterInUseException(message);
  }

  public static Error Error(CloudHsmClusterInvalidConfigurationException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_CloudHsmClusterInvalidConfigurationException(message);
  }

  public static Error Error(NotFoundException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_NotFoundException(message);
  }

  public static Error Error(LimitExceededException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_LimitExceededException(message);
  }

  public static Error Error(IncorrectKeyMaterialException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_IncorrectKeyMaterialException(message);
  }

  public static Error Error(KMSInvalidSignatureException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_KMSInvalidSignatureException(message);
  }

  public static Error Error(IncorrectTrustAnchorException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_IncorrectTrustAnchorException(message);
  }

  public static Error Error(KMSInternalException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_KMSInternalException(message);
  }

  public static Error Error(InvalidCiphertextException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_InvalidCiphertextException(message);
  }

  public static Error Error(AWSKMSException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message = Objects.nonNull(nativeValue.getMessage()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
        : Option.create_None();
    return new Error_Opaque(message);
  }

  public static EncryptionAlgorithmSpec EncryptionAlgorithmSpec(
      com.amazonaws.services.kms.model.EncryptionAlgorithmSpec nativeValue) {
    switch (nativeValue) {
      case SYMMETRIC_DEFAULT: {
        return EncryptionAlgorithmSpec.create_SYMMETRIC__DEFAULT();
      }
      case RSAES_OAEP_SHA_1: {
        return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1();
      }
      case RSAES_OAEP_SHA_256: {
        return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.EncryptionAlgorithmSpec.");
      }
    }
  }

  public static DataKeyPairSpec DataKeyPairSpec(
      com.amazonaws.services.kms.model.DataKeyPairSpec nativeValue) {
    switch (nativeValue) {
      case RSA_2048: {
        return DataKeyPairSpec.create_RSA__2048();
      }
      case RSA_3072: {
        return DataKeyPairSpec.create_RSA__3072();
      }
      case RSA_4096: {
        return DataKeyPairSpec.create_RSA__4096();
      }
      case ECC_NIST_P256: {
        return DataKeyPairSpec.create_ECC__NIST__P256();
      }
      case ECC_NIST_P384: {
        return DataKeyPairSpec.create_ECC__NIST__P384();
      }
      case ECC_NIST_P521: {
        return DataKeyPairSpec.create_ECC__NIST__P521();
      }
      case ECC_SECG_P256K1: {
        return DataKeyPairSpec.create_ECC__SECG__P256K1();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.DataKeyPairSpec.");
      }
    }
  }

  public static CustomerMasterKeySpec CustomerMasterKeySpec(
      com.amazonaws.services.kms.model.CustomerMasterKeySpec nativeValue) {
    switch (nativeValue) {
      case RSA_2048: {
        return CustomerMasterKeySpec.create_RSA__2048();
      }
      case RSA_3072: {
        return CustomerMasterKeySpec.create_RSA__3072();
      }
      case RSA_4096: {
        return CustomerMasterKeySpec.create_RSA__4096();
      }
      case ECC_NIST_P256: {
        return CustomerMasterKeySpec.create_ECC__NIST__P256();
      }
      case ECC_NIST_P384: {
        return CustomerMasterKeySpec.create_ECC__NIST__P384();
      }
      case ECC_NIST_P521: {
        return CustomerMasterKeySpec.create_ECC__NIST__P521();
      }
      case ECC_SECG_P256K1: {
        return CustomerMasterKeySpec.create_ECC__SECG__P256K1();
      }
      case SYMMETRIC_DEFAULT: {
        return CustomerMasterKeySpec.create_SYMMETRIC__DEFAULT();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.CustomerMasterKeySpec.");
      }
    }
  }

  public static KeySpec KeySpec(com.amazonaws.services.kms.model.KeySpec nativeValue) {
    switch (nativeValue) {
      case RSA_2048: {
        return KeySpec.create_RSA__2048();
      }
      case RSA_3072: {
        return KeySpec.create_RSA__3072();
      }
      case RSA_4096: {
        return KeySpec.create_RSA__4096();
      }
      case ECC_NIST_P256: {
        return KeySpec.create_ECC__NIST__P256();
      }
      case ECC_NIST_P384: {
        return KeySpec.create_ECC__NIST__P384();
      }
      case ECC_NIST_P521: {
        return KeySpec.create_ECC__NIST__P521();
      }
      case ECC_SECG_P256K1: {
        return KeySpec.create_ECC__SECG__P256K1();
      }
      case SYMMETRIC_DEFAULT: {
        return KeySpec.create_SYMMETRIC__DEFAULT();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.KeySpec.");
      }
    }
  }

  public static KeyUsageType KeyUsageType(
      com.amazonaws.services.kms.model.KeyUsageType nativeValue) {
    switch (nativeValue) {
      case SIGN_VERIFY: {
        return KeyUsageType.create_SIGN__VERIFY();
      }
      case ENCRYPT_DECRYPT: {
        return KeyUsageType.create_ENCRYPT__DECRYPT();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.KeyUsageType.");
      }
    }
  }

  public static KeyState KeyState(com.amazonaws.services.kms.model.KeyState nativeValue) {
    switch (nativeValue) {
      case Creating: {
        return KeyState.create_Creating();
      }
      case Enabled: {
        return KeyState.create_Enabled();
      }
      case Disabled: {
        return KeyState.create_Disabled();
      }
      case PendingDeletion: {
        return KeyState.create_PendingDeletion();
      }
      case PendingImport: {
        return KeyState.create_PendingImport();
      }
      case PendingReplicaDeletion: {
        return KeyState.create_PendingReplicaDeletion();
      }
      case Unavailable: {
        return KeyState.create_Unavailable();
      }
      case Updating: {
        return KeyState.create_Updating();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.KeyState.");
      }
    }
  }

  public static SigningAlgorithmSpec SigningAlgorithmSpec(
      com.amazonaws.services.kms.model.SigningAlgorithmSpec nativeValue) {
    switch (nativeValue) {
      case RSASSA_PSS_SHA_256: {
        return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__256();
      }
      case RSASSA_PSS_SHA_384: {
        return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__384();
      }
      case RSASSA_PSS_SHA_512: {
        return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__512();
      }
      case RSASSA_PKCS1_V1_5_SHA_256: {
        return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__256();
      }
      case RSASSA_PKCS1_V1_5_SHA_384: {
        return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__384();
      }
      case RSASSA_PKCS1_V1_5_SHA_512: {
        return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__512();
      }
      case ECDSA_SHA_256: {
        return SigningAlgorithmSpec.create_ECDSA__SHA__256();
      }
      case ECDSA_SHA_384: {
        return SigningAlgorithmSpec.create_ECDSA__SHA__384();
      }
      case ECDSA_SHA_512: {
        return SigningAlgorithmSpec.create_ECDSA__SHA__512();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.SigningAlgorithmSpec.");
      }
    }
  }

  public static OriginType OriginType(com.amazonaws.services.kms.model.OriginType nativeValue) {
    switch (nativeValue) {
      case AWS_KMS: {
        return OriginType.create_AWS__KMS();
      }
      case EXTERNAL: {
        return OriginType.create_EXTERNAL();
      }
      case AWS_CLOUDHSM: {
        return OriginType.create_AWS__CLOUDHSM();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.OriginType.");
      }
    }
  }

  public static ExpirationModelType ExpirationModelType(
      com.amazonaws.services.kms.model.ExpirationModelType nativeValue) {
    switch (nativeValue) {
      case KEY_MATERIAL_EXPIRES: {
        return ExpirationModelType.create_KEY__MATERIAL__EXPIRES();
      }
      case KEY_MATERIAL_DOES_NOT_EXPIRE: {
        return ExpirationModelType.create_KEY__MATERIAL__DOES__NOT__EXPIRE();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.ExpirationModelType.");
      }
    }
  }

  public static KeyManagerType KeyManagerType(
      com.amazonaws.services.kms.model.KeyManagerType nativeValue) {
    switch (nativeValue) {
      case AWS: {
        return KeyManagerType.create_AWS();
      }
      case CUSTOMER: {
        return KeyManagerType.create_CUSTOMER();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.KeyManagerType.");
      }
    }
  }

  public static MultiRegionKeyType MultiRegionKeyType(
      com.amazonaws.services.kms.model.MultiRegionKeyType nativeValue) {
    switch (nativeValue) {
      case PRIMARY: {
        return MultiRegionKeyType.create_PRIMARY();
      }
      case REPLICA: {
        return MultiRegionKeyType.create_REPLICA();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.MultiRegionKeyType.");
      }
    }
  }

  public static ConnectionStateType ConnectionStateType(
      com.amazonaws.services.kms.model.ConnectionStateType nativeValue) {
    switch (nativeValue) {
      case CONNECTED: {
        return ConnectionStateType.create_CONNECTED();
      }
      case CONNECTING: {
        return ConnectionStateType.create_CONNECTING();
      }
      case FAILED: {
        return ConnectionStateType.create_FAILED();
      }
      case DISCONNECTED: {
        return ConnectionStateType.create_DISCONNECTED();
      }
      case DISCONNECTING: {
        return ConnectionStateType.create_DISCONNECTING();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.ConnectionStateType.");
      }
    }
  }

  public static ConnectionErrorCodeType ConnectionErrorCodeType(
      com.amazonaws.services.kms.model.ConnectionErrorCodeType nativeValue) {
    switch (nativeValue) {
      case INVALID_CREDENTIALS: {
        return ConnectionErrorCodeType.create_INVALID__CREDENTIALS();
      }
      case CLUSTER_NOT_FOUND: {
        return ConnectionErrorCodeType.create_CLUSTER__NOT__FOUND();
      }
      case NETWORK_ERRORS: {
        return ConnectionErrorCodeType.create_NETWORK__ERRORS();
      }
      case INTERNAL_ERROR: {
        return ConnectionErrorCodeType.create_INTERNAL__ERROR();
      }
      case INSUFFICIENT_CLOUDHSM_HSMS: {
        return ConnectionErrorCodeType.create_INSUFFICIENT__CLOUDHSM__HSMS();
      }
      case USER_LOCKED_OUT: {
        return ConnectionErrorCodeType.create_USER__LOCKED__OUT();
      }
      case USER_NOT_FOUND: {
        return ConnectionErrorCodeType.create_USER__NOT__FOUND();
      }
      case USER_LOGGED_IN: {
        return ConnectionErrorCodeType.create_USER__LOGGED__IN();
      }
      case SUBNET_NOT_FOUND: {
        return ConnectionErrorCodeType.create_SUBNET__NOT__FOUND();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.ConnectionErrorCodeType.");
      }
    }
  }

  public static GrantOperation GrantOperation(
      com.amazonaws.services.kms.model.GrantOperation nativeValue) {
    switch (nativeValue) {
      case Decrypt: {
        return GrantOperation.create_Decrypt();
      }
      case Encrypt: {
        return GrantOperation.create_Encrypt();
      }
      case GenerateDataKey: {
        return GrantOperation.create_GenerateDataKey();
      }
      case GenerateDataKeyWithoutPlaintext: {
        return GrantOperation.create_GenerateDataKeyWithoutPlaintext();
      }
      case ReEncryptFrom: {
        return GrantOperation.create_ReEncryptFrom();
      }
      case ReEncryptTo: {
        return GrantOperation.create_ReEncryptTo();
      }
      case Sign: {
        return GrantOperation.create_Sign();
      }
      case Verify: {
        return GrantOperation.create_Verify();
      }
      case GetPublicKey: {
        return GrantOperation.create_GetPublicKey();
      }
      case CreateGrant: {
        return GrantOperation.create_CreateGrant();
      }
      case RetireGrant: {
        return GrantOperation.create_RetireGrant();
      }
      case DescribeKey: {
        return GrantOperation.create_DescribeKey();
      }
      case GenerateDataKeyPair: {
        return GrantOperation.create_GenerateDataKeyPair();
      }
      case GenerateDataKeyPairWithoutPlaintext: {
        return GrantOperation.create_GenerateDataKeyPairWithoutPlaintext();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.GrantOperation.");
      }
    }
  }

  public static EncryptionAlgorithmSpec EncryptionAlgorithmSpec(String nativeValue) {
    return EncryptionAlgorithmSpec(com.amazonaws.services.kms.model.EncryptionAlgorithmSpec.fromValue(nativeValue));
  }

  public static DataKeyPairSpec DataKeyPairSpec(String nativeValue) {
    return DataKeyPairSpec(com.amazonaws.services.kms.model.DataKeyPairSpec.fromValue(nativeValue));
  }

  public static CustomerMasterKeySpec CustomerMasterKeySpec(String nativeValue) {
    return CustomerMasterKeySpec(com.amazonaws.services.kms.model.CustomerMasterKeySpec.fromValue(nativeValue));
  }

  public static KeySpec KeySpec(String nativeValue) {
    return KeySpec(com.amazonaws.services.kms.model.KeySpec.fromValue(nativeValue));
  }

  public static KeyUsageType KeyUsageType(String nativeValue) {
    return KeyUsageType(com.amazonaws.services.kms.model.KeyUsageType.fromValue(nativeValue));
  }

  public static KeyState KeyState(String nativeValue) {
    return KeyState(com.amazonaws.services.kms.model.KeyState.fromValue(nativeValue));
  }

  public static SigningAlgorithmSpec SigningAlgorithmSpec(String nativeValue) {
    return SigningAlgorithmSpec(com.amazonaws.services.kms.model.SigningAlgorithmSpec.fromValue(nativeValue));
  }

  public static OriginType OriginType(String nativeValue) {
    return OriginType(com.amazonaws.services.kms.model.OriginType.fromValue(nativeValue));
  }

  public static ExpirationModelType ExpirationModelType(String nativeValue) {
    return ExpirationModelType(com.amazonaws.services.kms.model.ExpirationModelType.fromValue(nativeValue));
  }

  public static KeyManagerType KeyManagerType(String nativeValue) {
    return KeyManagerType(com.amazonaws.services.kms.model.KeyManagerType.fromValue(nativeValue));
  }

  public static MultiRegionKeyType MultiRegionKeyType(String nativeValue) {
    return MultiRegionKeyType(com.amazonaws.services.kms.model.MultiRegionKeyType.fromValue(nativeValue));
  }

  public static ConnectionStateType ConnectionStateType(String nativeValue) {
    return ConnectionStateType(com.amazonaws.services.kms.model.ConnectionStateType.fromValue(nativeValue));
  }

  public static ConnectionErrorCodeType ConnectionErrorCodeType(String nativeValue) {
    return ConnectionErrorCodeType(com.amazonaws.services.kms.model.ConnectionErrorCodeType.fromValue(nativeValue));
  }

  public static GrantOperation GrantOperation(String nativeValue) {
    return GrantOperation(com.amazonaws.services.kms.model.GrantOperation.fromValue(nativeValue));
  }
}
