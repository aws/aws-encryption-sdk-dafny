// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package Dafny.Com.Amazonaws.Kms;

import Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionRequest;
import Dafny.Com.Amazonaws.Kms.Types.CancelKeyDeletionResponse;
import Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreRequest;
import Dafny.Com.Amazonaws.Kms.Types.ConnectCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.CreateAliasRequest;
import Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreRequest;
import Dafny.Com.Amazonaws.Kms.Types.CreateCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.CreateGrantRequest;
import Dafny.Com.Amazonaws.Kms.Types.CreateGrantResponse;
import Dafny.Com.Amazonaws.Kms.Types.CreateKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.CreateKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.DecryptRequest;
import Dafny.Com.Amazonaws.Kms.Types.DecryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.DeleteAliasRequest;
import Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreRequest;
import Dafny.Com.Amazonaws.Kms.Types.DeleteCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.DeleteImportedKeyMaterialRequest;
import Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresRequest;
import Dafny.Com.Amazonaws.Kms.Types.DescribeCustomKeyStoresResponse;
import Dafny.Com.Amazonaws.Kms.Types.DescribeKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.DescribeKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.DisableKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.DisableKeyRotationRequest;
import Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreRequest;
import Dafny.Com.Amazonaws.Kms.Types.DisconnectCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.EnableKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.EnableKeyRotationRequest;
import Dafny.Com.Amazonaws.Kms.Types.EncryptRequest;
import Dafny.Com.Amazonaws.Kms.Types.EncryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairRequest;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextRequest;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyPairWithoutPlaintextResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextRequest;
import Dafny.Com.Amazonaws.Kms.Types.GenerateDataKeyWithoutPlaintextResponse;
import Dafny.Com.Amazonaws.Kms.Types.GenerateRandomRequest;
import Dafny.Com.Amazonaws.Kms.Types.GenerateRandomResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyRequest;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyPolicyResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusRequest;
import Dafny.Com.Amazonaws.Kms.Types.GetKeyRotationStatusResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportRequest;
import Dafny.Com.Amazonaws.Kms.Types.GetParametersForImportResponse;
import Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.GetPublicKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialRequest;
import Dafny.Com.Amazonaws.Kms.Types.ImportKeyMaterialResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListAliasesRequest;
import Dafny.Com.Amazonaws.Kms.Types.ListAliasesResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListGrantsRequest;
import Dafny.Com.Amazonaws.Kms.Types.ListGrantsResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesRequest;
import Dafny.Com.Amazonaws.Kms.Types.ListKeyPoliciesResponse;
import Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsRequest;
import Dafny.Com.Amazonaws.Kms.Types.ListResourceTagsResponse;
import Dafny.Com.Amazonaws.Kms.Types.PutKeyPolicyRequest;
import Dafny.Com.Amazonaws.Kms.Types.ReEncryptRequest;
import Dafny.Com.Amazonaws.Kms.Types.ReEncryptResponse;
import Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyRequest;
import Dafny.Com.Amazonaws.Kms.Types.ReplicateKeyResponse;
import Dafny.Com.Amazonaws.Kms.Types.RetireGrantRequest;
import Dafny.Com.Amazonaws.Kms.Types.RevokeGrantRequest;
import Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionRequest;
import Dafny.Com.Amazonaws.Kms.Types.ScheduleKeyDeletionResponse;
import Dafny.Com.Amazonaws.Kms.Types.SignRequest;
import Dafny.Com.Amazonaws.Kms.Types.SignResponse;
import Dafny.Com.Amazonaws.Kms.Types.TagResourceRequest;
import Dafny.Com.Amazonaws.Kms.Types.UntagResourceRequest;
import Dafny.Com.Amazonaws.Kms.Types.UpdateAliasRequest;
import Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreRequest;
import Dafny.Com.Amazonaws.Kms.Types.UpdateCustomKeyStoreResponse;
import Dafny.Com.Amazonaws.Kms.Types.UpdateKeyDescriptionRequest;
import Dafny.Com.Amazonaws.Kms.Types.UpdatePrimaryRegionRequest;
import Dafny.Com.Amazonaws.Kms.Types.VerifyRequest;
import Dafny.Com.Amazonaws.Kms.Types.VerifyResponse;
import Wrappers_Compile.Result;
import com.amazonaws.services.kms.AWSKMS;
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
import dafny.Tuple0;
import java.lang.Override;
import java.lang.String;

public class Shim implements IKeyManagementServiceClient {
  private final AWSKMS _impl;

  private final String region;

  public Shim(final AWSKMS impl, final String region) {
    this._impl = impl;
    this.region = region;
  }

  public String region() {
    return this.region;
  }

  public AWSKMS impl() {
    return this._impl;
  }

  @Override
  public Result<CancelKeyDeletionResponse, Error> CancelKeyDeletion(
      CancelKeyDeletionRequest input) {
    com.amazonaws.services.kms.model.CancelKeyDeletionRequest converted = ToNative.CancelKeyDeletionRequest(input);
    try {
      CancelKeyDeletionResult result = _impl.cancelKeyDeletion(converted);
      CancelKeyDeletionResponse dafnyResponse = ToDafny.CancelKeyDeletionResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ConnectCustomKeyStoreResponse, Error> ConnectCustomKeyStore(
      ConnectCustomKeyStoreRequest input) {
    com.amazonaws.services.kms.model.ConnectCustomKeyStoreRequest converted = ToNative.ConnectCustomKeyStoreRequest(input);
    try {
      ConnectCustomKeyStoreResult result = _impl.connectCustomKeyStore(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> CreateAlias(CreateAliasRequest input) {
    com.amazonaws.services.kms.model.CreateAliasRequest converted = ToNative.CreateAliasRequest(input);
    try {
      _impl.createAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (AlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidAliasNameException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateCustomKeyStoreResponse, Error> CreateCustomKeyStore(
      CreateCustomKeyStoreRequest input) {
    com.amazonaws.services.kms.model.CreateCustomKeyStoreRequest converted = ToNative.CreateCustomKeyStoreRequest(input);
    try {
      CreateCustomKeyStoreResult result = _impl.createCustomKeyStore(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateGrantResponse, Error> CreateGrant(CreateGrantRequest input) {
    com.amazonaws.services.kms.model.CreateGrantRequest converted = ToNative.CreateGrantRequest(input);
    try {
      CreateGrantResult result = _impl.createGrant(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateKeyResponse, Error> CreateKey(CreateKeyRequest input) {
    com.amazonaws.services.kms.model.CreateKeyRequest converted = ToNative.CreateKeyRequest(input);
    try {
      CreateKeyResult result = _impl.createKey(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (MalformedPolicyDocumentException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DecryptResponse, Error> Decrypt(DecryptRequest input) {
    com.amazonaws.services.kms.model.DecryptRequest converted = ToNative.DecryptRequest(input);
    try {
      DecryptResult result = _impl.decrypt(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DeleteAlias(DeleteAliasRequest input) {
    com.amazonaws.services.kms.model.DeleteAliasRequest converted = ToNative.DeleteAliasRequest(input);
    try {
      _impl.deleteAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DeleteCustomKeyStoreResponse, Error> DeleteCustomKeyStore(
      DeleteCustomKeyStoreRequest input) {
    com.amazonaws.services.kms.model.DeleteCustomKeyStoreRequest converted = ToNative.DeleteCustomKeyStoreRequest(input);
    try {
      DeleteCustomKeyStoreResult result = _impl.deleteCustomKeyStore(converted);
      DeleteCustomKeyStoreResponse dafnyResponse = ToDafny.DeleteCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreHasCMKsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DeleteImportedKeyMaterial(DeleteImportedKeyMaterialRequest input) {
    com.amazonaws.services.kms.model.DeleteImportedKeyMaterialRequest converted = ToNative.DeleteImportedKeyMaterialRequest(input);
    try {
      _impl.deleteImportedKeyMaterial(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeCustomKeyStoresResponse, Error> DescribeCustomKeyStores(
      DescribeCustomKeyStoresRequest input) {
    com.amazonaws.services.kms.model.DescribeCustomKeyStoresRequest converted = ToNative.DescribeCustomKeyStoresRequest(input);
    try {
      DescribeCustomKeyStoresResult result = _impl.describeCustomKeyStores(converted);
      DescribeCustomKeyStoresResponse dafnyResponse = ToDafny.DescribeCustomKeyStoresResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeKeyResponse, Error> DescribeKey(DescribeKeyRequest input) {
    com.amazonaws.services.kms.model.DescribeKeyRequest converted = ToNative.DescribeKeyRequest(input);
    try {
      DescribeKeyResult result = _impl.describeKey(converted);
      DescribeKeyResponse dafnyResponse = ToDafny.DescribeKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DisableKey(DisableKeyRequest input) {
    com.amazonaws.services.kms.model.DisableKeyRequest converted = ToNative.DisableKeyRequest(input);
    try {
      _impl.disableKey(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> DisableKeyRotation(DisableKeyRotationRequest input) {
    com.amazonaws.services.kms.model.DisableKeyRotationRequest converted = ToNative.DisableKeyRotationRequest(input);
    try {
      _impl.disableKeyRotation(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DisconnectCustomKeyStoreResponse, Error> DisconnectCustomKeyStore(
      DisconnectCustomKeyStoreRequest input) {
    com.amazonaws.services.kms.model.DisconnectCustomKeyStoreRequest converted = ToNative.DisconnectCustomKeyStoreRequest(input);
    try {
      DisconnectCustomKeyStoreResult result = _impl.disconnectCustomKeyStore(converted);
      DisconnectCustomKeyStoreResponse dafnyResponse = ToDafny.DisconnectCustomKeyStoreResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> EnableKey(EnableKeyRequest input) {
    com.amazonaws.services.kms.model.EnableKeyRequest converted = ToNative.EnableKeyRequest(input);
    try {
      _impl.enableKey(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> EnableKeyRotation(EnableKeyRotationRequest input) {
    com.amazonaws.services.kms.model.EnableKeyRotationRequest converted = ToNative.EnableKeyRotationRequest(input);
    try {
      _impl.enableKeyRotation(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<EncryptResponse, Error> Encrypt(EncryptRequest input) {
    com.amazonaws.services.kms.model.EncryptRequest converted = ToNative.EncryptRequest(input);
    try {
      EncryptResult result = _impl.encrypt(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyResponse, Error> GenerateDataKey(GenerateDataKeyRequest input) {
    com.amazonaws.services.kms.model.GenerateDataKeyRequest converted = ToNative.GenerateDataKeyRequest(input);
    try {
      GenerateDataKeyResult result = _impl.generateDataKey(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyPairResponse, Error> GenerateDataKeyPair(
      GenerateDataKeyPairRequest input) {
    com.amazonaws.services.kms.model.GenerateDataKeyPairRequest converted = ToNative.GenerateDataKeyPairRequest(input);
    try {
      GenerateDataKeyPairResult result = _impl.generateDataKeyPair(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyPairWithoutPlaintextResponse, Error> GenerateDataKeyPairWithoutPlaintext(
      GenerateDataKeyPairWithoutPlaintextRequest input) {
    com.amazonaws.services.kms.model.GenerateDataKeyPairWithoutPlaintextRequest converted = ToNative.GenerateDataKeyPairWithoutPlaintextRequest(input);
    try {
      GenerateDataKeyPairWithoutPlaintextResult result = _impl.generateDataKeyPairWithoutPlaintext(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateDataKeyWithoutPlaintextResponse, Error> GenerateDataKeyWithoutPlaintext(
      GenerateDataKeyWithoutPlaintextRequest input) {
    com.amazonaws.services.kms.model.GenerateDataKeyWithoutPlaintextRequest converted = ToNative.GenerateDataKeyWithoutPlaintextRequest(input);
    try {
      GenerateDataKeyWithoutPlaintextResult result = _impl.generateDataKeyWithoutPlaintext(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GenerateRandomResponse, Error> GenerateRandom(GenerateRandomRequest input) {
    com.amazonaws.services.kms.model.GenerateRandomRequest converted = ToNative.GenerateRandomRequest(input);
    try {
      GenerateRandomResult result = _impl.generateRandom(converted);
      GenerateRandomResponse dafnyResponse = ToDafny.GenerateRandomResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (CustomKeyStoreInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (CustomKeyStoreNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetKeyPolicyResponse, Error> GetKeyPolicy(GetKeyPolicyRequest input) {
    com.amazonaws.services.kms.model.GetKeyPolicyRequest converted = ToNative.GetKeyPolicyRequest(input);
    try {
      GetKeyPolicyResult result = _impl.getKeyPolicy(converted);
      GetKeyPolicyResponse dafnyResponse = ToDafny.GetKeyPolicyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetKeyRotationStatusResponse, Error> GetKeyRotationStatus(
      GetKeyRotationStatusRequest input) {
    com.amazonaws.services.kms.model.GetKeyRotationStatusRequest converted = ToNative.GetKeyRotationStatusRequest(input);
    try {
      GetKeyRotationStatusResult result = _impl.getKeyRotationStatus(converted);
      GetKeyRotationStatusResponse dafnyResponse = ToDafny.GetKeyRotationStatusResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetParametersForImportResponse, Error> GetParametersForImport(
      GetParametersForImportRequest input) {
    com.amazonaws.services.kms.model.GetParametersForImportRequest converted = ToNative.GetParametersForImportRequest(input);
    try {
      GetParametersForImportResult result = _impl.getParametersForImport(converted);
      GetParametersForImportResponse dafnyResponse = ToDafny.GetParametersForImportResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetPublicKeyResponse, Error> GetPublicKey(GetPublicKeyRequest input) {
    com.amazonaws.services.kms.model.GetPublicKeyRequest converted = ToNative.GetPublicKeyRequest(input);
    try {
      GetPublicKeyResult result = _impl.getPublicKey(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ImportKeyMaterialResponse, Error> ImportKeyMaterial(
      ImportKeyMaterialRequest input) {
    com.amazonaws.services.kms.model.ImportKeyMaterialRequest converted = ToNative.ImportKeyMaterialRequest(input);
    try {
      ImportKeyMaterialResult result = _impl.importKeyMaterial(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListAliasesResponse, Error> ListAliases(ListAliasesRequest input) {
    com.amazonaws.services.kms.model.ListAliasesRequest converted = ToNative.ListAliasesRequest(input);
    try {
      ListAliasesResult result = _impl.listAliases(converted);
      ListAliasesResponse dafnyResponse = ToDafny.ListAliasesResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListGrantsResponse, Error> ListGrants(ListGrantsRequest input) {
    com.amazonaws.services.kms.model.ListGrantsRequest converted = ToNative.ListGrantsRequest(input);
    try {
      ListGrantsResult result = _impl.listGrants(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListKeyPoliciesResponse, Error> ListKeyPolicies(ListKeyPoliciesRequest input) {
    com.amazonaws.services.kms.model.ListKeyPoliciesRequest converted = ToNative.ListKeyPoliciesRequest(input);
    try {
      ListKeyPoliciesResult result = _impl.listKeyPolicies(converted);
      ListKeyPoliciesResponse dafnyResponse = ToDafny.ListKeyPoliciesResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListResourceTagsResponse, Error> ListResourceTags(ListResourceTagsRequest input) {
    com.amazonaws.services.kms.model.ListResourceTagsRequest converted = ToNative.ListResourceTagsRequest(input);
    try {
      ListResourceTagsResult result = _impl.listResourceTags(converted);
      ListResourceTagsResponse dafnyResponse = ToDafny.ListResourceTagsResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidMarkerException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> PutKeyPolicy(PutKeyPolicyRequest input) {
    com.amazonaws.services.kms.model.PutKeyPolicyRequest converted = ToNative.PutKeyPolicyRequest(input);
    try {
      _impl.putKeyPolicy(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (MalformedPolicyDocumentException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ReEncryptResponse, Error> ReEncrypt(ReEncryptRequest input) {
    com.amazonaws.services.kms.model.ReEncryptRequest converted = ToNative.ReEncryptRequest(input);
    try {
      ReEncryptResult result = _impl.reEncrypt(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ReplicateKeyResponse, Error> ReplicateKey(ReplicateKeyRequest input) {
    com.amazonaws.services.kms.model.ReplicateKeyRequest converted = ToNative.ReplicateKeyRequest(input);
    try {
      ReplicateKeyResult result = _impl.replicateKey(converted);
      ReplicateKeyResponse dafnyResponse = ToDafny.ReplicateKeyResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (AlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
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
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> RetireGrant(RetireGrantRequest input) {
    com.amazonaws.services.kms.model.RetireGrantRequest converted = ToNative.RetireGrantRequest(input);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> RevokeGrant(RevokeGrantRequest input) {
    com.amazonaws.services.kms.model.RevokeGrantRequest converted = ToNative.RevokeGrantRequest(input);
    try {
      _impl.revokeGrant(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidGrantIdException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ScheduleKeyDeletionResponse, Error> ScheduleKeyDeletion(
      ScheduleKeyDeletionRequest input) {
    com.amazonaws.services.kms.model.ScheduleKeyDeletionRequest converted = ToNative.ScheduleKeyDeletionRequest(input);
    try {
      ScheduleKeyDeletionResult result = _impl.scheduleKeyDeletion(converted);
      ScheduleKeyDeletionResponse dafnyResponse = ToDafny.ScheduleKeyDeletionResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<SignResponse, Error> Sign(SignRequest input) {
    com.amazonaws.services.kms.model.SignRequest converted = ToNative.SignRequest(input);
    try {
      SignResult result = _impl.sign(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> TagResource(TagResourceRequest input) {
    com.amazonaws.services.kms.model.TagResourceRequest converted = ToNative.TagResourceRequest(input);
    try {
      _impl.tagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UntagResource(UntagResourceRequest input) {
    com.amazonaws.services.kms.model.UntagResourceRequest converted = ToNative.UntagResourceRequest(input);
    try {
      _impl.untagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TagException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdateAlias(UpdateAliasRequest input) {
    com.amazonaws.services.kms.model.UpdateAliasRequest converted = ToNative.UpdateAliasRequest(input);
    try {
      _impl.updateAlias(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateCustomKeyStoreResponse, Error> UpdateCustomKeyStore(
      UpdateCustomKeyStoreRequest input) {
    com.amazonaws.services.kms.model.UpdateCustomKeyStoreRequest converted = ToNative.UpdateCustomKeyStoreRequest(input);
    try {
      UpdateCustomKeyStoreResult result = _impl.updateCustomKeyStore(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdateKeyDescription(UpdateKeyDescriptionRequest input) {
    com.amazonaws.services.kms.model.UpdateKeyDescriptionRequest converted = ToNative.UpdateKeyDescriptionRequest(input);
    try {
      _impl.updateKeyDescription(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DependencyTimeoutException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UpdatePrimaryRegion(UpdatePrimaryRegionRequest input) {
    com.amazonaws.services.kms.model.UpdatePrimaryRegionRequest converted = ToNative.UpdatePrimaryRegionRequest(input);
    try {
      _impl.updatePrimaryRegion(converted);
      return Result.create_Success(Tuple0.create());
    } catch (DisabledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidArnException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (UnsupportedOperationException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<VerifyResponse, Error> Verify(VerifyRequest input) {
    com.amazonaws.services.kms.model.VerifyRequest converted = ToNative.VerifyRequest(input);
    try {
      VerifyResult result = _impl.verify(converted);
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
    } catch (KMSInternalException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidSignatureException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (KMSInvalidStateException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (NotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (AWSKMSException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }
}
