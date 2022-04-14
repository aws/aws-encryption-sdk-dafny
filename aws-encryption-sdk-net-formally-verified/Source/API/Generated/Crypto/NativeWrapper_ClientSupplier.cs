// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
// ReSharper disable once RedundantUsingDirective
using AWS.EncryptionSDK.Core;

// ReSharper disable once RedundantUsingDirective
using Wrappers_Compile;

namespace AWS.EncryptionSDK.Core
{
    internal class NativeWrapper_ClientSupplier : NativeWrapper_ClientSupplierBase
    {
        public NativeWrapper_ClientSupplier(IClientSupplier native_impl) : base(native_impl)
        { }

        public override _IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> GetClient(
            Dafny.Aws.EncryptionSdk.Core._IGetClientInput input)
        {
            var nativeInput = TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(input);
            try
            {
                var nativeOutput = _impl.GetClient(nativeInput);
                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Success(
                    TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(
                        nativeOutput)
                );
            }
            catch (AwsCryptographicMaterialProvidersBaseException e)
            {
                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                    TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(e)
                );
            }
            catch (Exception e)
            {
                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                    TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                        new AwsCryptographicMaterialProvidersException(e.Message))
                );
            }
        }
    }
}
