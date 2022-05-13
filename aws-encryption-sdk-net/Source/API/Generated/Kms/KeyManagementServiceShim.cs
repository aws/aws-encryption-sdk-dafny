// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;

namespace Com.Amazonaws.Kms
{
    internal class KeyManagementServiceShim : Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
    {
        internal Amazon.KeyManagementService.AmazonKeyManagementServiceClient _impl;

        internal KeyManagementServiceShim(Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl)
        {
            this._impl = impl;
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> CancelKeyDeletion(
            Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionRequest request)
        {
            Amazon.KeyManagementService.Model.CancelKeyDeletionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CancelKeyDeletionResponse sdkResponse =
                    this._impl.CancelKeyDeletionAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ConnectCustomKeyStore(
            Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse sdkResponse =
                    this._impl.ConnectCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            CreateAlias(Dafny.Com.Amazonaws.Kms._ICreateAliasRequest request)
        {
            Amazon.KeyManagementService.Model.CreateAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(request);
            try
            {
                this._impl.CreateAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> CreateCustomKeyStore(
            Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse sdkResponse =
                    this._impl.CreateCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._ICreateGrantResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> CreateGrant(
            Dafny.Com.Amazonaws.Kms._ICreateGrantRequest request)
        {
            Amazon.KeyManagementService.Model.CreateGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateGrantResponse sdkResponse =
                    this._impl.CreateGrantAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateGrantResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateGrantResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._ICreateKeyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> CreateKey(
            Dafny.Com.Amazonaws.Kms._ICreateKeyRequest request)
        {
            Amazon.KeyManagementService.Model.CreateKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateKeyResponse sdkResponse =
                    this._impl.CreateKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ICreateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IDecryptResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> Decrypt(
            Dafny.Com.Amazonaws.Kms._IDecryptRequest request)
        {
            Amazon.KeyManagementService.Model.DecryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DecryptResponse sdkResponse =
                    this._impl.DecryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDecryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDecryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            DeleteAlias(Dafny.Com.Amazonaws.Kms._IDeleteAliasRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(request);
            try
            {
                this._impl.DeleteAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> DeleteCustomKeyStore(
            Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse sdkResponse =
                    this._impl.DeleteCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            DeleteImportedKeyMaterial(Dafny.Com.Amazonaws.Kms._IDeleteImportedKeyMaterialRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(request);
            try
            {
                this._impl.DeleteImportedKeyMaterialAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> DescribeCustomKeyStores(
            Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresRequest request)
        {
            Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse sdkResponse =
                    this._impl.DescribeCustomKeyStoresAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IDescribeKeyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> DescribeKey(
            Dafny.Com.Amazonaws.Kms._IDescribeKeyRequest request)
        {
            Amazon.KeyManagementService.Model.DescribeKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DescribeKeyResponse sdkResponse =
                    this._impl.DescribeKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDescribeKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDescribeKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            DisableKey(Dafny.Com.Amazonaws.Kms._IDisableKeyRequest request)
        {
            Amazon.KeyManagementService.Model.DisableKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(request);
            try
            {
                this._impl.DisableKeyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            DisableKeyRotation(Dafny.Com.Amazonaws.Kms._IDisableKeyRotationRequest request)
        {
            Amazon.KeyManagementService.Model.DisableKeyRotationRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(request);
            try
            {
                this._impl.DisableKeyRotationAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> DisconnectCustomKeyStore(
            Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse sdkResponse =
                    this._impl.DisconnectCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            EnableKey(Dafny.Com.Amazonaws.Kms._IEnableKeyRequest request)
        {
            Amazon.KeyManagementService.Model.EnableKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(request);
            try
            {
                this._impl.EnableKeyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            EnableKeyRotation(Dafny.Com.Amazonaws.Kms._IEnableKeyRotationRequest request)
        {
            Amazon.KeyManagementService.Model.EnableKeyRotationRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(request);
            try
            {
                this._impl.EnableKeyRotationAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IEncryptResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> Encrypt(
            Dafny.Com.Amazonaws.Kms._IEncryptRequest request)
        {
            Amazon.KeyManagementService.Model.EncryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.EncryptResponse sdkResponse =
                    this._impl.EncryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GenerateDataKey(
            Dafny.Com.Amazonaws.Kms._IGenerateDataKeyRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyResponse sdkResponse =
                    this._impl.GenerateDataKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GenerateDataKeyPair(
            Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse sdkResponse =
                    this._impl.GenerateDataKeyPairAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GenerateDataKeyPairWithoutPlaintext(
            Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(
                    request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse sdkResponse =
                    this._impl.GenerateDataKeyPairWithoutPlaintextAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(
                                sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GenerateDataKeyWithoutPlaintext(
            Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(
                    request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse sdkResponse =
                    this._impl.GenerateDataKeyWithoutPlaintextAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(
                                sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGenerateRandomResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GenerateRandom(
            Dafny.Com.Amazonaws.Kms._IGenerateRandomRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateRandomRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateRandomResponse sdkResponse =
                    this._impl.GenerateRandomAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateRandomResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGenerateRandomResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGetKeyPolicyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GetKeyPolicy(
            Dafny.Com.Amazonaws.Kms._IGetKeyPolicyRequest request)
        {
            Amazon.KeyManagementService.Model.GetKeyPolicyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetKeyPolicyResponse sdkResponse =
                    this._impl.GetKeyPolicyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetKeyPolicyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetKeyPolicyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GetKeyRotationStatus(
            Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusRequest request)
        {
            Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse sdkResponse =
                    this._impl.GetKeyRotationStatusAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGetParametersForImportResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GetParametersForImport(
            Dafny.Com.Amazonaws.Kms._IGetParametersForImportRequest request)
        {
            Amazon.KeyManagementService.Model.GetParametersForImportRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetParametersForImportResponse sdkResponse =
                    this._impl.GetParametersForImportAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetParametersForImportResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetParametersForImportResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IGetPublicKeyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> GetPublicKey(
            Dafny.Com.Amazonaws.Kms._IGetPublicKeyRequest request)
        {
            Amazon.KeyManagementService.Model.GetPublicKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetPublicKeyResponse sdkResponse =
                    this._impl.GetPublicKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetPublicKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IGetPublicKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IImportKeyMaterialResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ImportKeyMaterial(
            Dafny.Com.Amazonaws.Kms._IImportKeyMaterialRequest request)
        {
            Amazon.KeyManagementService.Model.ImportKeyMaterialRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ImportKeyMaterialResponse sdkResponse =
                    this._impl.ImportKeyMaterialAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IImportKeyMaterialResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IImportKeyMaterialResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IListAliasesResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ListAliases(
            Dafny.Com.Amazonaws.Kms._IListAliasesRequest request)
        {
            Amazon.KeyManagementService.Model.ListAliasesRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListAliasesResponse sdkResponse =
                    this._impl.ListAliasesAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListAliasesResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListAliasesResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IListGrantsResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ListGrants(
            Dafny.Com.Amazonaws.Kms._IListGrantsRequest request)
        {
            Amazon.KeyManagementService.Model.ListGrantsRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListGrantsResponse sdkResponse =
                    this._impl.ListGrantsAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListGrantsResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListGrantsResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IListKeyPoliciesResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ListKeyPolicies(
            Dafny.Com.Amazonaws.Kms._IListKeyPoliciesRequest request)
        {
            Amazon.KeyManagementService.Model.ListKeyPoliciesRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListKeyPoliciesResponse sdkResponse =
                    this._impl.ListKeyPoliciesAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListKeyPoliciesResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListKeyPoliciesResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IListResourceTagsResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ListResourceTags(
            Dafny.Com.Amazonaws.Kms._IListResourceTagsRequest request)
        {
            Amazon.KeyManagementService.Model.ListResourceTagsRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListResourceTagsResponse sdkResponse =
                    this._impl.ListResourceTagsAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListResourceTagsResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IListResourceTagsResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            PutKeyPolicy(Dafny.Com.Amazonaws.Kms._IPutKeyPolicyRequest request)
        {
            Amazon.KeyManagementService.Model.PutKeyPolicyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(request);
            try
            {
                this._impl.PutKeyPolicyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IReEncryptResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ReEncrypt(
            Dafny.Com.Amazonaws.Kms._IReEncryptRequest request)
        {
            Amazon.KeyManagementService.Model.ReEncryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ReEncryptResponse sdkResponse =
                    this._impl.ReEncryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IReEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IReEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IReplicateKeyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ReplicateKey(
            Dafny.Com.Amazonaws.Kms._IReplicateKeyRequest request)
        {
            Amazon.KeyManagementService.Model.ReplicateKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ReplicateKeyResponse sdkResponse =
                    this._impl.ReplicateKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IReplicateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IReplicateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            RetireGrant(Dafny.Com.Amazonaws.Kms._IRetireGrantRequest request)
        {
            Amazon.KeyManagementService.Model.RetireGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(request);
            try
            {
                this._impl.RetireGrantAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            RevokeGrant(Dafny.Com.Amazonaws.Kms._IRevokeGrantRequest request)
        {
            Amazon.KeyManagementService.Model.RevokeGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(request);
            try
            {
                this._impl.RevokeGrantAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> ScheduleKeyDeletion(
            Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionRequest request)
        {
            Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse sdkResponse =
                    this._impl.ScheduleKeyDeletionAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._ISignResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> Sign(Dafny.Com.Amazonaws.Kms._ISignRequest request)
        {
            Amazon.KeyManagementService.Model.SignRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.SignResponse sdkResponse =
                    this._impl.SignAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ISignResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._ISignResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            TagResource(Dafny.Com.Amazonaws.Kms._ITagResourceRequest request)
        {
            Amazon.KeyManagementService.Model.TagResourceRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(request);
            try
            {
                this._impl.TagResourceAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            UntagResource(Dafny.Com.Amazonaws.Kms._IUntagResourceRequest request)
        {
            Amazon.KeyManagementService.Model.UntagResourceRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(request);
            try
            {
                this._impl.UntagResourceAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            UpdateAlias(Dafny.Com.Amazonaws.Kms._IUpdateAliasRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(request);
            try
            {
                this._impl.UpdateAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> UpdateCustomKeyStore(
            Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse sdkResponse =
                    this._impl.UpdateCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            UpdateKeyDescription(Dafny.Com.Amazonaws.Kms._IUpdateKeyDescriptionRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(request);
            try
            {
                this._impl.UpdateKeyDescriptionAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
            UpdatePrimaryRegion(Dafny.Com.Amazonaws.Kms._IUpdatePrimaryRegionRequest request)
        {
            Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(request);
            try
            {
                this._impl.UpdatePrimaryRegionAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Success(_System.Tuple0.Default());
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms._IVerifyResponse,
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException> Verify(
            Dafny.Com.Amazonaws.Kms._IVerifyRequest request)
        {
            Amazon.KeyManagementService.Model.VerifyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.VerifyResponse sdkResponse =
                    this._impl.VerifyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IVerifyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(sdkResponse));
            }
            catch (System.AggregateException aggregate) when (aggregate.InnerException is
                Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms._IVerifyResponse,
                        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException>.create_Failure(this.ConvertError(ex));
            }
        }

        private Dafny.Com.Amazonaws.Kms.IKeyManagementServiceException ConvertError(
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
                    return TypeConversion
                        .ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(e);

                case Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException e:
                    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(e);

                case Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException e:
                    return TypeConversion
                        .ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(e);

                case Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException e:
                    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(e);

                case Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException e:
                    return TypeConversion
                        .ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(e);

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
                    return new Dafny.Com.Amazonaws.Kms.UnknownKeyManagementServiceError
                    {
                        message = TypeConversion.ToDafny_N6_smithy__N3_api__S6_String(error.Message ?? "")
                    };
            }
        }
    }
}
