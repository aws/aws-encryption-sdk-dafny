// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> CancelKeyDeletion(
            Dafny.Com.Amazonaws.Kms.CancelKeyDeletionRequest request)
        {
            Amazon.KeyManagementService.Model.CancelKeyDeletionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CancelKeyDeletionResponse sdkResponse =
                    this._impl.CancelKeyDeletionAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ConnectCustomKeyStore(
            Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse sdkResponse =
                    this._impl.ConnectCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> CreateAlias(
            Dafny.Com.Amazonaws.Kms.CreateAliasRequest request)
        {
            Amazon.KeyManagementService.Model.CreateAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(request);
            try
            {
                this._impl.CreateAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> CreateCustomKeyStore(
            Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse sdkResponse =
                    this._impl.CreateCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.CreateGrantResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> CreateGrant(
            Dafny.Com.Amazonaws.Kms.CreateGrantRequest request)
        {
            Amazon.KeyManagementService.Model.CreateGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateGrantResponse sdkResponse =
                    this._impl.CreateGrantAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateGrantResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateGrantResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.CreateKeyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> CreateKey(
            Dafny.Com.Amazonaws.Kms.CreateKeyRequest request)
        {
            Amazon.KeyManagementService.Model.CreateKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.CreateKeyResponse sdkResponse =
                    this._impl.CreateKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.CreateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.DecryptResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> Decrypt(Dafny.Com.Amazonaws.Kms.DecryptRequest request)
        {
            Amazon.KeyManagementService.Model.DecryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DecryptResponse sdkResponse =
                    this._impl.DecryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DecryptResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DecryptResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DeleteAlias(
            Dafny.Com.Amazonaws.Kms.DeleteAliasRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(request);
            try
            {
                this._impl.DeleteAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DeleteCustomKeyStore(
            Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse sdkResponse =
                    this._impl.DeleteCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
            DeleteImportedKeyMaterial(Dafny.Com.Amazonaws.Kms.DeleteImportedKeyMaterialRequest request)
        {
            Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(request);
            try
            {
                this._impl.DeleteImportedKeyMaterialAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DescribeCustomKeyStores(
            Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresRequest request)
        {
            Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse sdkResponse =
                    this._impl.DescribeCustomKeyStoresAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.DescribeKeyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DescribeKey(
            Dafny.Com.Amazonaws.Kms.DescribeKeyRequest request)
        {
            Amazon.KeyManagementService.Model.DescribeKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DescribeKeyResponse sdkResponse =
                    this._impl.DescribeKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DescribeKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DescribeKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DisableKey(
            Dafny.Com.Amazonaws.Kms.DisableKeyRequest request)
        {
            Amazon.KeyManagementService.Model.DisableKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(request);
            try
            {
                this._impl.DisableKeyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
            DisableKeyRotation(Dafny.Com.Amazonaws.Kms.DisableKeyRotationRequest request)
        {
            Amazon.KeyManagementService.Model.DisableKeyRotationRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(request);
            try
            {
                this._impl.DisableKeyRotationAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> DisconnectCustomKeyStore(
            Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse sdkResponse =
                    this._impl.DisconnectCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> EnableKey(
            Dafny.Com.Amazonaws.Kms.EnableKeyRequest request)
        {
            Amazon.KeyManagementService.Model.EnableKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(request);
            try
            {
                this._impl.EnableKeyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
            EnableKeyRotation(Dafny.Com.Amazonaws.Kms.EnableKeyRotationRequest request)
        {
            Amazon.KeyManagementService.Model.EnableKeyRotationRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(request);
            try
            {
                this._impl.EnableKeyRotationAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.EncryptResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> Encrypt(Dafny.Com.Amazonaws.Kms.EncryptRequest request)
        {
            Amazon.KeyManagementService.Model.EncryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.EncryptResponse sdkResponse =
                    this._impl.EncryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.EncryptResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.EncryptResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GenerateDataKey(
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyResponse sdkResponse =
                    this._impl.GenerateDataKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GenerateDataKeyPair(
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse sdkResponse =
                    this._impl.GenerateDataKeyPairAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GenerateDataKeyPairWithoutPlaintext(
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(
                    request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse sdkResponse =
                    this._impl.GenerateDataKeyPairWithoutPlaintextAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(
                                sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GenerateDataKeyWithoutPlaintext(
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(
                    request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse sdkResponse =
                    this._impl.GenerateDataKeyWithoutPlaintextAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(
                                sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GenerateRandomResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GenerateRandom(
            Dafny.Com.Amazonaws.Kms.GenerateRandomRequest request)
        {
            Amazon.KeyManagementService.Model.GenerateRandomRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GenerateRandomResponse sdkResponse =
                    this._impl.GenerateRandomAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateRandomResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GenerateRandomResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GetKeyPolicy(
            Dafny.Com.Amazonaws.Kms.GetKeyPolicyRequest request)
        {
            Amazon.KeyManagementService.Model.GetKeyPolicyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetKeyPolicyResponse sdkResponse =
                    this._impl.GetKeyPolicyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GetKeyRotationStatus(
            Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusRequest request)
        {
            Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse sdkResponse =
                    this._impl.GetKeyRotationStatusAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GetParametersForImport(
            Dafny.Com.Amazonaws.Kms.GetParametersForImportRequest request)
        {
            Amazon.KeyManagementService.Model.GetParametersForImportRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetParametersForImportResponse sdkResponse =
                    this._impl.GetParametersForImportAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> GetPublicKey(
            Dafny.Com.Amazonaws.Kms.GetPublicKeyRequest request)
        {
            Amazon.KeyManagementService.Model.GetPublicKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.GetPublicKeyResponse sdkResponse =
                    this._impl.GetPublicKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ImportKeyMaterial(
            Dafny.Com.Amazonaws.Kms.ImportKeyMaterialRequest request)
        {
            Amazon.KeyManagementService.Model.ImportKeyMaterialRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ImportKeyMaterialResponse sdkResponse =
                    this._impl.ImportKeyMaterialAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ListAliasesResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ListAliases(
            Dafny.Com.Amazonaws.Kms.ListAliasesRequest request)
        {
            Amazon.KeyManagementService.Model.ListAliasesRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListAliasesResponse sdkResponse =
                    this._impl.ListAliasesAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListAliasesResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListAliasesResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ListGrantsResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ListGrants(
            Dafny.Com.Amazonaws.Kms.ListGrantsRequest request)
        {
            Amazon.KeyManagementService.Model.ListGrantsRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListGrantsResponse sdkResponse =
                    this._impl.ListGrantsAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListGrantsResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListGrantsResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ListKeyPolicies(
            Dafny.Com.Amazonaws.Kms.ListKeyPoliciesRequest request)
        {
            Amazon.KeyManagementService.Model.ListKeyPoliciesRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListKeyPoliciesResponse sdkResponse =
                    this._impl.ListKeyPoliciesAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ListResourceTags(
            Dafny.Com.Amazonaws.Kms.ListResourceTagsRequest request)
        {
            Amazon.KeyManagementService.Model.ListResourceTagsRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ListResourceTagsResponse sdkResponse =
                    this._impl.ListResourceTagsAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> PutKeyPolicy(
            Dafny.Com.Amazonaws.Kms.PutKeyPolicyRequest request)
        {
            Amazon.KeyManagementService.Model.PutKeyPolicyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(request);
            try
            {
                this._impl.PutKeyPolicyAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ReEncryptResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ReEncrypt(
            Dafny.Com.Amazonaws.Kms.ReEncryptRequest request)
        {
            Amazon.KeyManagementService.Model.ReEncryptRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ReEncryptResponse sdkResponse =
                    this._impl.ReEncryptAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ReEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ReEncryptResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ReplicateKey(
            Dafny.Com.Amazonaws.Kms.ReplicateKeyRequest request)
        {
            Amazon.KeyManagementService.Model.ReplicateKeyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ReplicateKeyResponse sdkResponse =
                    this._impl.ReplicateKeyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> RetireGrant(
            Dafny.Com.Amazonaws.Kms.RetireGrantRequest request)
        {
            Amazon.KeyManagementService.Model.RetireGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(request);
            try
            {
                this._impl.RetireGrantAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> RevokeGrant(
            Dafny.Com.Amazonaws.Kms.RevokeGrantRequest request)
        {
            Amazon.KeyManagementService.Model.RevokeGrantRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(request);
            try
            {
                this._impl.RevokeGrantAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> ScheduleKeyDeletion(
            Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionRequest request)
        {
            Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse sdkResponse =
                    this._impl.ScheduleKeyDeletionAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.SignResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> Sign(Dafny.Com.Amazonaws.Kms.SignRequest request)
        {
            Amazon.KeyManagementService.Model.SignRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.SignResponse sdkResponse =
                    this._impl.SignAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.SignResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.SignResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> TagResource(
            Dafny.Com.Amazonaws.Kms.TagResourceRequest request)
        {
            Amazon.KeyManagementService.Model.TagResourceRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(request);
            try
            {
                this._impl.TagResourceAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> UntagResource(
            Dafny.Com.Amazonaws.Kms.UntagResourceRequest request)
        {
            Amazon.KeyManagementService.Model.UntagResourceRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(request);
            try
            {
                this._impl.UntagResourceAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> UpdateAlias(
            Dafny.Com.Amazonaws.Kms.UpdateAliasRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateAliasRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(request);
            try
            {
                this._impl.UpdateAliasAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> UpdateCustomKeyStore(
            Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse sdkResponse =
                    this._impl.UpdateCustomKeyStoreAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(
                            sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse,
                        Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>.create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
            UpdateKeyDescription(Dafny.Com.Amazonaws.Kms.UpdateKeyDescriptionRequest request)
        {
            Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(request);
            try
            {
                this._impl.UpdateKeyDescriptionAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
            UpdatePrimaryRegion(Dafny.Com.Amazonaws.Kms.UpdatePrimaryRegionRequest request)
        {
            Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(request);
            try
            {
                this._impl.UpdatePrimaryRegionAsync(sdkRequest).Wait();
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(new _System.Tuple0());
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile.Result<_System.Tuple0, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        public Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.VerifyResponse,
            Dafny.Com.Amazonaws.Kms.KeyManagementServiceError> Verify(Dafny.Com.Amazonaws.Kms.VerifyRequest request)
        {
            Amazon.KeyManagementService.Model.VerifyRequest sdkRequest =
                TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(request);
            try
            {
                Amazon.KeyManagementService.Model.VerifyResponse sdkResponse =
                    this._impl.VerifyAsync(sdkRequest).Result;
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.VerifyResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Success(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(sdkResponse));
            }
            catch (Amazon.KeyManagementService.AmazonKeyManagementServiceException ex)
            {
                return Wrappers_Compile
                    .Result<Dafny.Com.Amazonaws.Kms.VerifyResponse, Dafny.Com.Amazonaws.Kms.KeyManagementServiceError>
                    .create_Failure(this.ConvertError(ex));
            }
        }

        private Dafny.Com.Amazonaws.Kms.KeyManagementServiceError ConvertError(
            Amazon.KeyManagementService.AmazonKeyManagementServiceException error)
        {
            if (error is Amazon.KeyManagementService.Model.AlreadyExistsException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__AlreadyExistsException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(
                            (Amazon.KeyManagementService.Model.AlreadyExistsException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CloudHsmClusterInUseException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CloudHsmClusterInUseException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(
                            (Amazon.KeyManagementService.Model.CloudHsmClusterInUseException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CloudHsmClusterInvalidConfigurationException(
                        TypeConversion
                            .ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(
                                (Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException)
                                error));
            }

            if (error is Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CloudHsmClusterNotActiveException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(
                            (Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CloudHsmClusterNotFoundException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(
                            (Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CloudHsmClusterNotRelatedException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(
                            (Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CustomKeyStoreHasCMKsException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(
                            (Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CustomKeyStoreInvalidStateException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(
                            (Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CustomKeyStoreNameInUseException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(
                            (Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException) error));
            }

            if (error is Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__CustomKeyStoreNotFoundException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(
                            (Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException) error));
            }

            if (error is Amazon.KeyManagementService.Model.DependencyTimeoutException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__DependencyTimeoutException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(
                            (Amazon.KeyManagementService.Model.DependencyTimeoutException) error));
            }

            if (error is Amazon.KeyManagementService.Model.DisabledException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError.create_KeyManagementService__DisabledException(
                    TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(
                        (Amazon.KeyManagementService.Model.DisabledException) error));
            }

            if (error is Amazon.KeyManagementService.Model.ExpiredImportTokenException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__ExpiredImportTokenException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(
                            (Amazon.KeyManagementService.Model.ExpiredImportTokenException) error));
            }

            if (error is Amazon.KeyManagementService.Model.IncorrectKeyException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__IncorrectKeyException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(
                            (Amazon.KeyManagementService.Model.IncorrectKeyException) error));
            }

            if (error is Amazon.KeyManagementService.Model.IncorrectKeyMaterialException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__IncorrectKeyMaterialException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(
                            (Amazon.KeyManagementService.Model.IncorrectKeyMaterialException) error));
            }

            if (error is Amazon.KeyManagementService.Model.IncorrectTrustAnchorException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__IncorrectTrustAnchorException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(
                            (Amazon.KeyManagementService.Model.IncorrectTrustAnchorException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidAliasNameException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidAliasNameException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(
                            (Amazon.KeyManagementService.Model.InvalidAliasNameException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidArnException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidArnException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(
                            (Amazon.KeyManagementService.Model.InvalidArnException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidCiphertextException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidCiphertextException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(
                            (Amazon.KeyManagementService.Model.InvalidCiphertextException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidGrantIdException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidGrantIdException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(
                            (Amazon.KeyManagementService.Model.InvalidGrantIdException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidGrantTokenException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidGrantTokenException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(
                            (Amazon.KeyManagementService.Model.InvalidGrantTokenException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidImportTokenException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidImportTokenException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(
                            (Amazon.KeyManagementService.Model.InvalidImportTokenException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidKeyUsageException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidKeyUsageException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(
                            (Amazon.KeyManagementService.Model.InvalidKeyUsageException) error));
            }

            if (error is Amazon.KeyManagementService.Model.InvalidMarkerException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__InvalidMarkerException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(
                            (Amazon.KeyManagementService.Model.InvalidMarkerException) error));
            }

            if (error is Amazon.KeyManagementService.Model.KeyUnavailableException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__KeyUnavailableException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(
                            (Amazon.KeyManagementService.Model.KeyUnavailableException) error));
            }

            if (error is Amazon.KeyManagementService.Model.KMSInternalException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__KMSInternalException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(
                            (Amazon.KeyManagementService.Model.KMSInternalException) error));
            }

            if (error is Amazon.KeyManagementService.Model.KMSInvalidSignatureException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__KMSInvalidSignatureException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(
                            (Amazon.KeyManagementService.Model.KMSInvalidSignatureException) error));
            }

            if (error is Amazon.KeyManagementService.Model.KMSInvalidStateException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__KMSInvalidStateException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(
                            (Amazon.KeyManagementService.Model.KMSInvalidStateException) error));
            }

            if (error is Amazon.KeyManagementService.Model.LimitExceededException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__LimitExceededException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(
                            (Amazon.KeyManagementService.Model.LimitExceededException) error));
            }

            if (error is Amazon.KeyManagementService.Model.MalformedPolicyDocumentException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__MalformedPolicyDocumentException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(
                            (Amazon.KeyManagementService.Model.MalformedPolicyDocumentException) error));
            }

            if (error is Amazon.KeyManagementService.Model.NotFoundException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError.create_KeyManagementService__NotFoundException(
                    TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(
                        (Amazon.KeyManagementService.Model.NotFoundException) error));
            }

            if (error is Amazon.KeyManagementService.Model.TagException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError.create_KeyManagementService__TagException(
                    TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(
                        (Amazon.KeyManagementService.Model.TagException) error));
            }

            if (error is Amazon.KeyManagementService.Model.UnsupportedOperationException)
            {
                return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError
                    .create_KeyManagementService__UnsupportedOperationException(
                        TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(
                            (Amazon.KeyManagementService.Model.UnsupportedOperationException) error));
            }

            return Dafny.Com.Amazonaws.Kms.KeyManagementServiceError.create_KeyManagementService__Unknown(
                TypeConversion.ToDafny_N6_smithy__N3_api__S6_String(error.Message));
        }
    }
}
