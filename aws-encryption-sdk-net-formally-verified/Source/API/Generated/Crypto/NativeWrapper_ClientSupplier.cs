// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

// ReSharper disable RedundantUsingDirective
using System;
using Amazon.KeyManagementService;
using AWS.EncryptionSDK.Core;
using Wrappers_Compile;

namespace AWS.EncryptionSDK.Core
{
    internal class NativeWrapper_ClientSupplier : Dafny.Aws.EncryptionSdk.Core.IClientSupplier
    {
        internal readonly ClientSupplierBase _impl;

        public NativeWrapper_ClientSupplier(ClientSupplierBase nativeImpl)
        {
            _impl = nativeImpl;
        }

        public Wrappers_Compile._IResult<
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
        > GetClient(Dafny.Aws.EncryptionSdk.Core._IGetClientInput input)
        {
            // ReSharper disable once RedundantNameQualifier
            AWS.EncryptionSDK.Core.GetClientInput nativeInput =
                TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(
                    input);
            try
            {
                // ReSharper disable once RedundantNameQualifier
                Amazon.KeyManagementService.IAmazonKeyManagementService nativeOutput = _impl.GetClient(nativeInput);
                return Wrappers_Compile.Result<
                    Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
                >.create_Success(
                    TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(
                        nativeOutput)
                );
            }
            catch (AwsCryptographicMaterialProvidersBaseException e)
            {
                return Wrappers_Compile.Result<
                    Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(e)
                );
            }
            catch (Exception e)
            {
                return Wrappers_Compile.Result<
                    Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                        new AwsCryptographicMaterialProvidersBaseException(e.Message))
                );
            }
        }
    }
}
