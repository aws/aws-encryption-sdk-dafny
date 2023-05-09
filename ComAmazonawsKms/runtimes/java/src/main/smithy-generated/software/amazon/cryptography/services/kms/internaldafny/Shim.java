// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.kms.internaldafny;

import Wrappers_Compile.Result;
import dafny.Tuple0;
import java.lang.Override;
import java.lang.String;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.model.AlreadyExistsException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterInUseException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterInvalidConfigurationException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotActiveException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotFoundException;
import software.amazon.awssdk.services.kms.model.CloudHsmClusterNotRelatedException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreHasCmKsException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreInvalidStateException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreNameInUseException;
import software.amazon.awssdk.services.kms.model.CustomKeyStoreNotFoundException;
import software.amazon.awssdk.services.kms.model.DependencyTimeoutException;
import software.amazon.awssdk.services.kms.model.DisabledException;
import software.amazon.awssdk.services.kms.model.ExpiredImportTokenException;
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
import software.amazon.awssdk.services.kms.model.KeyUnavailableException;
import software.amazon.awssdk.services.kms.model.KmsException;
import software.amazon.awssdk.services.kms.model.KmsInternalException;
import software.amazon.awssdk.services.kms.model.KmsInvalidSignatureException;
import software.amazon.awssdk.services.kms.model.KmsInvalidStateException;
import software.amazon.awssdk.services.kms.model.LimitExceededException;
import software.amazon.awssdk.services.kms.model.MalformedPolicyDocumentException;
import software.amazon.awssdk.services.kms.model.NotFoundException;
import software.amazon.awssdk.services.kms.model.TagException;
import software.amazon.awssdk.services.kms.model.UnsupportedOperationException;
import software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.Error;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;
import software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.SignRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.SignResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse;
import software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest;
import software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse;

public class Shim implements IKMSClient {
  private final KmsClient _impl;

  private final String region;

  public Shim(final KmsClient impl, final String region) {
    this._impl = impl;
    this.region = region;
  }

  public KmsClient impl() {
    return this._impl;
  }

  public String region() {
    return this.region;
  }

  @Override
  public Result<CancelKeyDeletionResponse, Error> CancelKeyDeletion(
      CancelKeyDeletionRequest input) {
    software.amazon.awssdk.services.kms.model.CancelKeyDeletionRequest converted = ToNative.CancelKeyDeletionRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.CancelKeyDeletionResponse result = _impl.cancelKeyDeletion(converted);
      CancelKeyDeletionResponse dafnyResponse = ToDafny.CancelKeyDeletionResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ConnectCustomKeyStoreResponse, Error> ConnectCustomKeyStore(
      ConnectCustomKeyStoreRequest input) {
    software.amazon.awssdk.services.kms.model.ConnectCustomKeyStoreRequest converted = ToNative.ConnectCustomKeyStoreRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ConnectCustomKeyStoreResponse result = _impl.connectCustomKeyStore(converted);
      ConnectCustomKeyStoreResponse dafnyResponse = ToDafny.ConnectCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CloudHsmClusterInvalidConfigurationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotActiveException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> CreateAlias(CreateAliasRequest input) {
    software.amazon.awssdk.services.kms.model.CreateAliasRequest converted = ToNative.CreateAliasRequest(input);
    try {
      _impl.createAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (AlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidAliasNameException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateCustomKeyStoreResponse, Error> CreateCustomKeyStore(
      CreateCustomKeyStoreRequest input) {
    software.amazon.awssdk.services.kms.model.CreateCustomKeyStoreRequest converted = ToNative.CreateCustomKeyStoreRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.CreateCustomKeyStoreResponse result = _impl.createCustomKeyStore(converted);
      CreateCustomKeyStoreResponse dafnyResponse = ToDafny.CreateCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CloudHsmClusterInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterInvalidConfigurationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotActiveException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNameInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (IncorrectTrustAnchorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateGrantResponse, Error> CreateGrant(CreateGrantRequest input) {
    software.amazon.awssdk.services.kms.model.CreateGrantRequest converted = ToNative.CreateGrantRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.CreateGrantResponse result = _impl.createGrant(converted);
      CreateGrantResponse dafnyResponse = ToDafny.CreateGrantResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateKeyResponse, Error> CreateKey(CreateKeyRequest input) {
    software.amazon.awssdk.services.kms.model.CreateKeyRequest converted = ToNative.CreateKeyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.CreateKeyResponse result = _impl.createKey(converted);
      CreateKeyResponse dafnyResponse = ToDafny.CreateKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CloudHsmClusterInvalidConfigurationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (MalformedPolicyDocumentException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DecryptResponse, Error> Decrypt(DecryptRequest input) {
    software.amazon.awssdk.services.kms.model.DecryptRequest converted = ToNative.DecryptRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.DecryptResponse result = _impl.decrypt(converted);
      DecryptResponse dafnyResponse = ToDafny.DecryptResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (IncorrectKeyException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidCiphertextException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DeleteAlias(DeleteAliasRequest input) {
    software.amazon.awssdk.services.kms.model.DeleteAliasRequest converted = ToNative.DeleteAliasRequest(input);
    try {
      _impl.deleteAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DeleteCustomKeyStoreResponse, Error> DeleteCustomKeyStore(
      DeleteCustomKeyStoreRequest input) {
    software.amazon.awssdk.services.kms.model.DeleteCustomKeyStoreRequest converted = ToNative.DeleteCustomKeyStoreRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.DeleteCustomKeyStoreResponse result = _impl.deleteCustomKeyStore(converted);
      DeleteCustomKeyStoreResponse dafnyResponse = ToDafny.DeleteCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreHasCmKsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DeleteImportedKeyMaterial(DeleteImportedKeyMaterialRequest input) {
    software.amazon.awssdk.services.kms.model.DeleteImportedKeyMaterialRequest converted = ToNative.DeleteImportedKeyMaterialRequest(input);
    try {
      _impl.deleteImportedKeyMaterial(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeCustomKeyStoresResponse, Error> DescribeCustomKeyStores(
      DescribeCustomKeyStoresRequest input) {
    software.amazon.awssdk.services.kms.model.DescribeCustomKeyStoresRequest converted = ToNative.DescribeCustomKeyStoresRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.DescribeCustomKeyStoresResponse result = _impl.describeCustomKeyStores(converted);
      DescribeCustomKeyStoresResponse dafnyResponse = ToDafny.DescribeCustomKeyStoresResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeKeyResponse, Error> DescribeKey(DescribeKeyRequest input) {
    software.amazon.awssdk.services.kms.model.DescribeKeyRequest converted = ToNative.DescribeKeyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.DescribeKeyResponse result = _impl.describeKey(converted);
      DescribeKeyResponse dafnyResponse = ToDafny.DescribeKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DisableKey(DisableKeyRequest input) {
    software.amazon.awssdk.services.kms.model.DisableKeyRequest converted = ToNative.DisableKeyRequest(input);
    try {
      _impl.disableKey(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DisableKeyRotation(DisableKeyRotationRequest input) {
    software.amazon.awssdk.services.kms.model.DisableKeyRotationRequest converted = ToNative.DisableKeyRotationRequest(input);
    try {
      _impl.disableKeyRotation(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DisconnectCustomKeyStoreResponse, Error> DisconnectCustomKeyStore(
      DisconnectCustomKeyStoreRequest input) {
    software.amazon.awssdk.services.kms.model.DisconnectCustomKeyStoreRequest converted = ToNative.DisconnectCustomKeyStoreRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.DisconnectCustomKeyStoreResponse result = _impl.disconnectCustomKeyStore(converted);
      DisconnectCustomKeyStoreResponse dafnyResponse = ToDafny.DisconnectCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> EnableKey(EnableKeyRequest input) {
    software.amazon.awssdk.services.kms.model.EnableKeyRequest converted = ToNative.EnableKeyRequest(input);
    try {
      _impl.enableKey(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> EnableKeyRotation(EnableKeyRotationRequest input) {
    software.amazon.awssdk.services.kms.model.EnableKeyRotationRequest converted = ToNative.EnableKeyRotationRequest(input);
    try {
      _impl.enableKeyRotation(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<EncryptResponse, Error> Encrypt(EncryptRequest input) {
    software.amazon.awssdk.services.kms.model.EncryptRequest converted = ToNative.EncryptRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.EncryptResponse result = _impl.encrypt(converted);
      EncryptResponse dafnyResponse = ToDafny.EncryptResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyResponse, Error> GenerateDataKey(GenerateDataKeyRequest input) {
    software.amazon.awssdk.services.kms.model.GenerateDataKeyRequest converted = ToNative.GenerateDataKeyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GenerateDataKeyResponse result = _impl.generateDataKey(converted);
      GenerateDataKeyResponse dafnyResponse = ToDafny.GenerateDataKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyPairResponse, Error> GenerateDataKeyPair(
      GenerateDataKeyPairRequest input) {
    software.amazon.awssdk.services.kms.model.GenerateDataKeyPairRequest converted = ToNative.GenerateDataKeyPairRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GenerateDataKeyPairResponse result = _impl.generateDataKeyPair(converted);
      GenerateDataKeyPairResponse dafnyResponse = ToDafny.GenerateDataKeyPairResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyPairWithoutPlaintextResponse, Error> GenerateDataKeyPairWithoutPlaintext(
      GenerateDataKeyPairWithoutPlaintextRequest input) {
    software.amazon.awssdk.services.kms.model.GenerateDataKeyPairWithoutPlaintextRequest converted = ToNative.GenerateDataKeyPairWithoutPlaintextRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GenerateDataKeyPairWithoutPlaintextResponse result = _impl.generateDataKeyPairWithoutPlaintext(converted);
      GenerateDataKeyPairWithoutPlaintextResponse dafnyResponse = ToDafny.GenerateDataKeyPairWithoutPlaintextResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyWithoutPlaintextResponse, Error> GenerateDataKeyWithoutPlaintext(
      GenerateDataKeyWithoutPlaintextRequest input) {
    software.amazon.awssdk.services.kms.model.GenerateDataKeyWithoutPlaintextRequest converted = ToNative.GenerateDataKeyWithoutPlaintextRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GenerateDataKeyWithoutPlaintextResponse result = _impl.generateDataKeyWithoutPlaintext(converted);
      GenerateDataKeyWithoutPlaintextResponse dafnyResponse = ToDafny.GenerateDataKeyWithoutPlaintextResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateRandomResponse, Error> GenerateRandom(GenerateRandomRequest input) {
    software.amazon.awssdk.services.kms.model.GenerateRandomRequest converted = ToNative.GenerateRandomRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GenerateRandomResponse result = _impl.generateRandom(converted);
      GenerateRandomResponse dafnyResponse = ToDafny.GenerateRandomResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetKeyPolicyResponse, Error> GetKeyPolicy(GetKeyPolicyRequest input) {
    software.amazon.awssdk.services.kms.model.GetKeyPolicyRequest converted = ToNative.GetKeyPolicyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GetKeyPolicyResponse result = _impl.getKeyPolicy(converted);
      GetKeyPolicyResponse dafnyResponse = ToDafny.GetKeyPolicyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetKeyRotationStatusResponse, Error> GetKeyRotationStatus(
      GetKeyRotationStatusRequest input) {
    software.amazon.awssdk.services.kms.model.GetKeyRotationStatusRequest converted = ToNative.GetKeyRotationStatusRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GetKeyRotationStatusResponse result = _impl.getKeyRotationStatus(converted);
      GetKeyRotationStatusResponse dafnyResponse = ToDafny.GetKeyRotationStatusResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetParametersForImportResponse, Error> GetParametersForImport(
      GetParametersForImportRequest input) {
    software.amazon.awssdk.services.kms.model.GetParametersForImportRequest converted = ToNative.GetParametersForImportRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GetParametersForImportResponse result = _impl.getParametersForImport(converted);
      GetParametersForImportResponse dafnyResponse = ToDafny.GetParametersForImportResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetPublicKeyResponse, Error> GetPublicKey(GetPublicKeyRequest input) {
    software.amazon.awssdk.services.kms.model.GetPublicKeyRequest converted = ToNative.GetPublicKeyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.GetPublicKeyResponse result = _impl.getPublicKey(converted);
      GetPublicKeyResponse dafnyResponse = ToDafny.GetPublicKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ImportKeyMaterialResponse, Error> ImportKeyMaterial(
      ImportKeyMaterialRequest input) {
    software.amazon.awssdk.services.kms.model.ImportKeyMaterialRequest converted = ToNative.ImportKeyMaterialRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ImportKeyMaterialResponse result = _impl.importKeyMaterial(converted);
      ImportKeyMaterialResponse dafnyResponse = ToDafny.ImportKeyMaterialResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ExpiredImportTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (IncorrectKeyMaterialException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidCiphertextException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidImportTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListAliasesResponse, Error> ListAliases(ListAliasesRequest input) {
    software.amazon.awssdk.services.kms.model.ListAliasesRequest converted = ToNative.ListAliasesRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ListAliasesResponse result = _impl.listAliases(converted);
      ListAliasesResponse dafnyResponse = ToDafny.ListAliasesResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListGrantsResponse, Error> ListGrants(ListGrantsRequest input) {
    software.amazon.awssdk.services.kms.model.ListGrantsRequest converted = ToNative.ListGrantsRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ListGrantsResponse result = _impl.listGrants(converted);
      ListGrantsResponse dafnyResponse = ToDafny.ListGrantsResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantIdException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListKeyPoliciesResponse, Error> ListKeyPolicies(ListKeyPoliciesRequest input) {
    software.amazon.awssdk.services.kms.model.ListKeyPoliciesRequest converted = ToNative.ListKeyPoliciesRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ListKeyPoliciesResponse result = _impl.listKeyPolicies(converted);
      ListKeyPoliciesResponse dafnyResponse = ToDafny.ListKeyPoliciesResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListResourceTagsResponse, Error> ListResourceTags(ListResourceTagsRequest input) {
    software.amazon.awssdk.services.kms.model.ListResourceTagsRequest converted = ToNative.ListResourceTagsRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ListResourceTagsResponse result = _impl.listResourceTags(converted);
      ListResourceTagsResponse dafnyResponse = ToDafny.ListResourceTagsResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> PutKeyPolicy(PutKeyPolicyRequest input) {
    software.amazon.awssdk.services.kms.model.PutKeyPolicyRequest converted = ToNative.PutKeyPolicyRequest(input);
    try {
      _impl.putKeyPolicy(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (MalformedPolicyDocumentException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ReEncryptResponse, Error> ReEncrypt(ReEncryptRequest input) {
    software.amazon.awssdk.services.kms.model.ReEncryptRequest converted = ToNative.ReEncryptRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ReEncryptResponse result = _impl.reEncrypt(converted);
      ReEncryptResponse dafnyResponse = ToDafny.ReEncryptResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (IncorrectKeyException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidCiphertextException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ReplicateKeyResponse, Error> ReplicateKey(ReplicateKeyRequest input) {
    software.amazon.awssdk.services.kms.model.ReplicateKeyRequest converted = ToNative.ReplicateKeyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ReplicateKeyResponse result = _impl.replicateKey(converted);
      ReplicateKeyResponse dafnyResponse = ToDafny.ReplicateKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (AlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (MalformedPolicyDocumentException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> RetireGrant(RetireGrantRequest input) {
    software.amazon.awssdk.services.kms.model.RetireGrantRequest converted = ToNative.RetireGrantRequest(input);
    try {
      _impl.retireGrant(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantIdException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> RevokeGrant(RevokeGrantRequest input) {
    software.amazon.awssdk.services.kms.model.RevokeGrantRequest converted = ToNative.RevokeGrantRequest(input);
    try {
      _impl.revokeGrant(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantIdException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ScheduleKeyDeletionResponse, Error> ScheduleKeyDeletion(
      ScheduleKeyDeletionRequest input) {
    software.amazon.awssdk.services.kms.model.ScheduleKeyDeletionRequest converted = ToNative.ScheduleKeyDeletionRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.ScheduleKeyDeletionResponse result = _impl.scheduleKeyDeletion(converted);
      ScheduleKeyDeletionResponse dafnyResponse = ToDafny.ScheduleKeyDeletionResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<SignResponse, Error> Sign(SignRequest input) {
    software.amazon.awssdk.services.kms.model.SignRequest converted = ToNative.SignRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.SignResponse result = _impl.sign(converted);
      SignResponse dafnyResponse = ToDafny.SignResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> TagResource(TagResourceRequest input) {
    software.amazon.awssdk.services.kms.model.TagResourceRequest converted = ToNative.TagResourceRequest(input);
    try {
      _impl.tagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UntagResource(UntagResourceRequest input) {
    software.amazon.awssdk.services.kms.model.UntagResourceRequest converted = ToNative.UntagResourceRequest(input);
    try {
      _impl.untagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdateAlias(UpdateAliasRequest input) {
    software.amazon.awssdk.services.kms.model.UpdateAliasRequest converted = ToNative.UpdateAliasRequest(input);
    try {
      _impl.updateAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateCustomKeyStoreResponse, Error> UpdateCustomKeyStore(
      UpdateCustomKeyStoreRequest input) {
    software.amazon.awssdk.services.kms.model.UpdateCustomKeyStoreRequest converted = ToNative.UpdateCustomKeyStoreRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.UpdateCustomKeyStoreResponse result = _impl.updateCustomKeyStore(converted);
      UpdateCustomKeyStoreResponse dafnyResponse = ToDafny.UpdateCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CloudHsmClusterInvalidConfigurationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotActiveException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CloudHsmClusterNotRelatedException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNameInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdateKeyDescription(UpdateKeyDescriptionRequest input) {
    software.amazon.awssdk.services.kms.model.UpdateKeyDescriptionRequest converted = ToNative.UpdateKeyDescriptionRequest(input);
    try {
      _impl.updateKeyDescription(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdatePrimaryRegion(UpdatePrimaryRegionRequest input) {
    software.amazon.awssdk.services.kms.model.UpdatePrimaryRegionRequest converted = ToNative.UpdatePrimaryRegionRequest(input);
    try {
      _impl.updatePrimaryRegion(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<VerifyResponse, Error> Verify(VerifyRequest input) {
    software.amazon.awssdk.services.kms.model.VerifyRequest converted = ToNative.VerifyRequest(input);
    try {
      software.amazon.awssdk.services.kms.model.VerifyResponse result = _impl.verify(converted);
      VerifyResponse dafnyResponse = ToDafny.VerifyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantTokenException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidKeyUsageException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KeyUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidSignatureException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KmsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }
}
