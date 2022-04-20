// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// ReSharper disable RedundantUsingDirective
// ReSharper disable RedundantNameQualifier
// ReSharper disable SuggestVarOrType_SimpleTypes

using System;
using AWS.EncryptionSDK.Core;
using Wrappers_Compile;

namespace AWS.EncryptionSDK.Core
{
    internal class NativeWrapper_Keyring : Dafny.Aws.EncryptionSdk.Core.IKeyring
    {
        internal readonly KeyringBase _impl;

        public NativeWrapper_Keyring(KeyringBase nativeImpl)
        {
            _impl = nativeImpl;
        }

        public Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> OnDecrypt(
            Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput input)
        {
            AWS.EncryptionSDK.Core.OnDecryptInput nativeInput =
                TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(input);
            try
            {
                AWS.EncryptionSDK.Core.OnDecryptOutput nativeOutput = _impl.OnDecrypt(nativeInput);
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>
                    .create_Success(
                        TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(nativeOutput));
            }
            catch (AwsCryptographicMaterialProvidersBaseException e)
            {
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>
                    .create_Failure(
                        TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(e));
            }
            catch (Exception e)
            {
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                        TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                            new AwsCryptographicMaterialProvidersBaseException(e.Message)));
            }
        }

        public Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> OnEncrypt(
            Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput input)
        {
            AWS.EncryptionSDK.Core.OnEncryptInput nativeInput =
                TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(input);
            try
            {
                AWS.EncryptionSDK.Core.OnEncryptOutput nativeOutput = _impl.OnEncrypt(nativeInput);
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>
                    .create_Success(
                        TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(nativeOutput));
            }
            catch (AwsCryptographicMaterialProvidersBaseException e)
            {
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>
                    .create_Failure(
                        TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(e));
            }
            catch (Exception e)
            {
                return Wrappers_Compile
                    .Result<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
                        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                        TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                            new AwsCryptographicMaterialProvidersBaseException(e.Message)));
            }
        }
    }
}
