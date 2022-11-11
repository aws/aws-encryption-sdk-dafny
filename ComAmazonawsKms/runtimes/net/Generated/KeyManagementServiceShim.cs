// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;

namespace Com.Amazonaws.Kms
{
  internal class KeyManagementServiceShim : Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient
  {
    internal Amazon.KeyManagementService.AmazonKeyManagementServiceClient _impl;

    internal KeyManagementServiceShim(Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl)
    {
      this._impl = impl;
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._ICancelKeyDeletionResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> CancelKeyDeletion(
      Dafny.Com.Amazonaws.Kms.Types._ICancelKeyDeletionRequest request)
    {
      Amazon.KeyManagementService.Model.CancelKeyDeletionRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.CancelKeyDeletionResponse sdkResponse =
          this._impl.CancelKeyDeletionAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICancelKeyDeletionResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICancelKeyDeletionResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IConnectCustomKeyStoreResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ConnectCustomKeyStore(
      Dafny.Com.Amazonaws.Kms.Types._IConnectCustomKeyStoreRequest request)
    {
      Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse sdkResponse =
          this._impl.ConnectCustomKeyStoreAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IConnectCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IConnectCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> CreateAlias(
      Dafny.Com.Amazonaws.Kms.Types._ICreateAliasRequest request)
    {
      Amazon.KeyManagementService.Model.CreateAliasRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(request);
      try
      {
        this._impl.CreateAliasAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._ICreateCustomKeyStoreResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> CreateCustomKeyStore(
      Dafny.Com.Amazonaws.Kms.Types._ICreateCustomKeyStoreRequest request)
    {
      Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse sdkResponse =
          this._impl.CreateCustomKeyStoreAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._ICreateGrantResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> CreateGrant(Dafny.Com.Amazonaws.Kms.Types._ICreateGrantRequest request)
    {
      Amazon.KeyManagementService.Model.CreateGrantRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.CreateGrantResponse sdkResponse =
          this._impl.CreateGrantAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateGrantResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateGrantResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._ICreateKeyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> CreateKey(Dafny.Com.Amazonaws.Kms.Types._ICreateKeyRequest request)
    {
      Amazon.KeyManagementService.Model.CreateKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.CreateKeyResponse sdkResponse =
          this._impl.CreateKeyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ICreateKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IDecryptResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> Decrypt(Dafny.Com.Amazonaws.Kms.Types._IDecryptRequest request)
    {
      Amazon.KeyManagementService.Model.DecryptRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.DecryptResponse sdkResponse =
          this._impl.DecryptAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDecryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDecryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> DeleteAlias(
      Dafny.Com.Amazonaws.Kms.Types._IDeleteAliasRequest request)
    {
      Amazon.KeyManagementService.Model.DeleteAliasRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(request);
      try
      {
        this._impl.DeleteAliasAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IDeleteCustomKeyStoreResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> DeleteCustomKeyStore(
      Dafny.Com.Amazonaws.Kms.Types._IDeleteCustomKeyStoreRequest request)
    {
      Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse sdkResponse =
          this._impl.DeleteCustomKeyStoreAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDeleteCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDeleteCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> DeleteImportedKeyMaterial(
      Dafny.Com.Amazonaws.Kms.Types._IDeleteImportedKeyMaterialRequest request)
    {
      Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(request);
      try
      {
        this._impl.DeleteImportedKeyMaterialAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IDescribeCustomKeyStoresResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> DescribeCustomKeyStores(
      Dafny.Com.Amazonaws.Kms.Types._IDescribeCustomKeyStoresRequest request)
    {
      Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse sdkResponse =
          this._impl.DescribeCustomKeyStoresAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDescribeCustomKeyStoresResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDescribeCustomKeyStoresResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IDescribeKeyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> DescribeKey(Dafny.Com.Amazonaws.Kms.Types._IDescribeKeyRequest request)
    {
      Amazon.KeyManagementService.Model.DescribeKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.DescribeKeyResponse sdkResponse =
          this._impl.DescribeKeyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDescribeKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDescribeKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> DisableKey(
      Dafny.Com.Amazonaws.Kms.Types._IDisableKeyRequest request)
    {
      Amazon.KeyManagementService.Model.DisableKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(request);
      try
      {
        this._impl.DisableKeyAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> DisableKeyRotation(
      Dafny.Com.Amazonaws.Kms.Types._IDisableKeyRotationRequest request)
    {
      Amazon.KeyManagementService.Model.DisableKeyRotationRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(request);
      try
      {
        this._impl.DisableKeyRotationAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IDisconnectCustomKeyStoreResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> DisconnectCustomKeyStore(
      Dafny.Com.Amazonaws.Kms.Types._IDisconnectCustomKeyStoreRequest request)
    {
      Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse sdkResponse =
          this._impl.DisconnectCustomKeyStoreAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDisconnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IDisconnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> EnableKey(
      Dafny.Com.Amazonaws.Kms.Types._IEnableKeyRequest request)
    {
      Amazon.KeyManagementService.Model.EnableKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(request);
      try
      {
        this._impl.EnableKeyAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> EnableKeyRotation(
      Dafny.Com.Amazonaws.Kms.Types._IEnableKeyRotationRequest request)
    {
      Amazon.KeyManagementService.Model.EnableKeyRotationRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(request);
      try
      {
        this._impl.EnableKeyRotationAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IEncryptResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> Encrypt(Dafny.Com.Amazonaws.Kms.Types._IEncryptRequest request)
    {
      Amazon.KeyManagementService.Model.EncryptRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.EncryptResponse sdkResponse =
          this._impl.EncryptAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IEncryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IEncryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GenerateDataKey(
      Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyRequest request)
    {
      Amazon.KeyManagementService.Model.GenerateDataKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GenerateDataKeyResponse sdkResponse =
          this._impl.GenerateDataKeyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GenerateDataKeyPair(
      Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairRequest request)
    {
      Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse sdkResponse =
          this._impl.GenerateDataKeyPairAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairWithoutPlaintextResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GenerateDataKeyPairWithoutPlaintext(
      Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairWithoutPlaintextRequest request)
    {
      Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse sdkResponse =
          this._impl.GenerateDataKeyPairWithoutPlaintextAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(
              sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyPairWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyWithoutPlaintextResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GenerateDataKeyWithoutPlaintext(
      Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyWithoutPlaintextRequest request)
    {
      Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse sdkResponse =
          this._impl.GenerateDataKeyWithoutPlaintextAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(
              sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateDataKeyWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGenerateRandomResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GenerateRandom(
      Dafny.Com.Amazonaws.Kms.Types._IGenerateRandomRequest request)
    {
      Amazon.KeyManagementService.Model.GenerateRandomRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GenerateRandomResponse sdkResponse =
          this._impl.GenerateRandomAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateRandomResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGenerateRandomResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGetKeyPolicyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GetKeyPolicy(Dafny.Com.Amazonaws.Kms.Types._IGetKeyPolicyRequest request)
    {
      Amazon.KeyManagementService.Model.GetKeyPolicyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GetKeyPolicyResponse sdkResponse =
          this._impl.GetKeyPolicyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetKeyPolicyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetKeyPolicyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGetKeyRotationStatusResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GetKeyRotationStatus(
      Dafny.Com.Amazonaws.Kms.Types._IGetKeyRotationStatusRequest request)
    {
      Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse sdkResponse =
          this._impl.GetKeyRotationStatusAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetKeyRotationStatusResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetKeyRotationStatusResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGetParametersForImportResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GetParametersForImport(
      Dafny.Com.Amazonaws.Kms.Types._IGetParametersForImportRequest request)
    {
      Amazon.KeyManagementService.Model.GetParametersForImportRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GetParametersForImportResponse sdkResponse =
          this._impl.GetParametersForImportAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetParametersForImportResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetParametersForImportResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IGetPublicKeyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> GetPublicKey(Dafny.Com.Amazonaws.Kms.Types._IGetPublicKeyRequest request)
    {
      Amazon.KeyManagementService.Model.GetPublicKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.GetPublicKeyResponse sdkResponse =
          this._impl.GetPublicKeyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetPublicKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IGetPublicKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IImportKeyMaterialResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ImportKeyMaterial(
      Dafny.Com.Amazonaws.Kms.Types._IImportKeyMaterialRequest request)
    {
      Amazon.KeyManagementService.Model.ImportKeyMaterialRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ImportKeyMaterialResponse sdkResponse =
          this._impl.ImportKeyMaterialAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IImportKeyMaterialResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IImportKeyMaterialResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IListAliasesResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ListAliases(Dafny.Com.Amazonaws.Kms.Types._IListAliasesRequest request)
    {
      Amazon.KeyManagementService.Model.ListAliasesRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ListAliasesResponse sdkResponse =
          this._impl.ListAliasesAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListAliasesResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListAliasesResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IListGrantsResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ListGrants(Dafny.Com.Amazonaws.Kms.Types._IListGrantsRequest request)
    {
      Amazon.KeyManagementService.Model.ListGrantsRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ListGrantsResponse sdkResponse =
          this._impl.ListGrantsAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListGrantsResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListGrantsResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IListKeyPoliciesResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ListKeyPolicies(
      Dafny.Com.Amazonaws.Kms.Types._IListKeyPoliciesRequest request)
    {
      Amazon.KeyManagementService.Model.ListKeyPoliciesRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ListKeyPoliciesResponse sdkResponse =
          this._impl.ListKeyPoliciesAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListKeyPoliciesResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListKeyPoliciesResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IListResourceTagsResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ListResourceTags(
      Dafny.Com.Amazonaws.Kms.Types._IListResourceTagsRequest request)
    {
      Amazon.KeyManagementService.Model.ListResourceTagsRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ListResourceTagsResponse sdkResponse =
          this._impl.ListResourceTagsAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListResourceTagsResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IListResourceTagsResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> PutKeyPolicy(
      Dafny.Com.Amazonaws.Kms.Types._IPutKeyPolicyRequest request)
    {
      Amazon.KeyManagementService.Model.PutKeyPolicyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(request);
      try
      {
        this._impl.PutKeyPolicyAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IReEncryptResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ReEncrypt(Dafny.Com.Amazonaws.Kms.Types._IReEncryptRequest request)
    {
      Amazon.KeyManagementService.Model.ReEncryptRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ReEncryptResponse sdkResponse =
          this._impl.ReEncryptAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IReEncryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IReEncryptResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IReplicateKeyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ReplicateKey(Dafny.Com.Amazonaws.Kms.Types._IReplicateKeyRequest request)
    {
      Amazon.KeyManagementService.Model.ReplicateKeyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ReplicateKeyResponse sdkResponse =
          this._impl.ReplicateKeyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IReplicateKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IReplicateKeyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> RetireGrant(
      Dafny.Com.Amazonaws.Kms.Types._IRetireGrantRequest request)
    {
      Amazon.KeyManagementService.Model.RetireGrantRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(request);
      try
      {
        this._impl.RetireGrantAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> RevokeGrant(
      Dafny.Com.Amazonaws.Kms.Types._IRevokeGrantRequest request)
    {
      Amazon.KeyManagementService.Model.RevokeGrantRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(request);
      try
      {
        this._impl.RevokeGrantAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IScheduleKeyDeletionResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> ScheduleKeyDeletion(
      Dafny.Com.Amazonaws.Kms.Types._IScheduleKeyDeletionRequest request)
    {
      Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse sdkResponse =
          this._impl.ScheduleKeyDeletionAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IScheduleKeyDeletionResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IScheduleKeyDeletionResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._ISignResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> Sign(Dafny.Com.Amazonaws.Kms.Types._ISignRequest request)
    {
      Amazon.KeyManagementService.Model.SignRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.SignResponse sdkResponse =
          this._impl.SignAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ISignResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._ISignResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> TagResource(
      Dafny.Com.Amazonaws.Kms.Types._ITagResourceRequest request)
    {
      Amazon.KeyManagementService.Model.TagResourceRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(request);
      try
      {
        this._impl.TagResourceAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> UntagResource(
      Dafny.Com.Amazonaws.Kms.Types._IUntagResourceRequest request)
    {
      Amazon.KeyManagementService.Model.UntagResourceRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(request);
      try
      {
        this._impl.UntagResourceAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> UpdateAlias(
      Dafny.Com.Amazonaws.Kms.Types._IUpdateAliasRequest request)
    {
      Amazon.KeyManagementService.Model.UpdateAliasRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(request);
      try
      {
        this._impl.UpdateAliasAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IUpdateCustomKeyStoreResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> UpdateCustomKeyStore(
      Dafny.Com.Amazonaws.Kms.Types._IUpdateCustomKeyStoreRequest request)
    {
      Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse sdkResponse =
          this._impl.UpdateCustomKeyStoreAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IUpdateCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(
            TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IUpdateCustomKeyStoreResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> UpdateKeyDescription(
      Dafny.Com.Amazonaws.Kms.Types._IUpdateKeyDescriptionRequest request)
    {
      Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(request);
      try
      {
        this._impl.UpdateKeyDescriptionAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError> UpdatePrimaryRegion(
      Dafny.Com.Amazonaws.Kms.Types._IUpdatePrimaryRegionRequest request)
    {
      Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(request);
      try
      {
        this._impl.UpdatePrimaryRegionAsync(sdkRequest).Wait();
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Success(
          _System.Tuple0.Default());
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.Types._IError>.create_Failure(
          this.ConvertError(ex));
      }
    }

    public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types._IVerifyResponse,
      Dafny.Com.Amazonaws.Kms.Types._IError> Verify(Dafny.Com.Amazonaws.Kms.Types._IVerifyRequest request)
    {
      Amazon.KeyManagementService.Model.VerifyRequest sdkRequest =
        TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(request);
      try
      {
        Amazon.KeyManagementService.Model.VerifyResponse sdkResponse =
          this._impl.VerifyAsync(sdkRequest).Result;
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IVerifyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(sdkResponse));
      }
      catch (System.AggregateException aggregate) when (aggregate.InnerException is
        Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
      {
        return Wrappers_Compile
          .Result<Dafny.Com.Amazonaws.Kms.Types._IVerifyResponse, Dafny.Com.Amazonaws.Kms.Types._IError>
          .create_Failure(this.ConvertError(ex));
      }
    }

    private Dafny.Com.Amazonaws.Kms.Types._IError ConvertError(
      Amazon.KeyManagementService.AmazonKeyManagementServiceException error)
    {
      switch (error)
      {
        case Amazon.KeyManagementService.Model.AlreadyExistsException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(e);

        case Amazon.KeyManagementService.Model.CloudHsmClusterInUseException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(e);

        case Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException e:
          return TypeConversion
            .ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(e);

        case Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(e);

        case Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(e);

        case Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(e);

        case Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(e);

        case Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(e);

        case Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(e);

        case Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(e);

        case Amazon.KeyManagementService.Model.DependencyTimeoutException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(e);

        case Amazon.KeyManagementService.Model.DisabledException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(e);

        case Amazon.KeyManagementService.Model.ExpiredImportTokenException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(e);

        case Amazon.KeyManagementService.Model.IncorrectKeyException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(e);

        case Amazon.KeyManagementService.Model.IncorrectKeyMaterialException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(e);

        case Amazon.KeyManagementService.Model.IncorrectTrustAnchorException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(e);

        case Amazon.KeyManagementService.Model.InvalidAliasNameException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(e);

        case Amazon.KeyManagementService.Model.InvalidArnException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(e);

        case Amazon.KeyManagementService.Model.InvalidCiphertextException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(e);

        case Amazon.KeyManagementService.Model.InvalidGrantIdException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(e);

        case Amazon.KeyManagementService.Model.InvalidGrantTokenException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(e);

        case Amazon.KeyManagementService.Model.InvalidImportTokenException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(e);

        case Amazon.KeyManagementService.Model.InvalidKeyUsageException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(e);

        case Amazon.KeyManagementService.Model.InvalidMarkerException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(e);

        case Amazon.KeyManagementService.Model.KeyUnavailableException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(e);

        case Amazon.KeyManagementService.Model.KMSInternalException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(e);

        case Amazon.KeyManagementService.Model.KMSInvalidSignatureException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(e);

        case Amazon.KeyManagementService.Model.KMSInvalidStateException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(e);

        case Amazon.KeyManagementService.Model.LimitExceededException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(e);

        case Amazon.KeyManagementService.Model.MalformedPolicyDocumentException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(e);

        case Amazon.KeyManagementService.Model.NotFoundException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(e);

        case Amazon.KeyManagementService.Model.TagException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(e);

        case Amazon.KeyManagementService.Model.UnsupportedOperationException e:
          return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(e);

        default:
          return new Dafny.Com.Amazonaws.Kms.Types.Error_Opaque(error);
      }
    }
  }
}
