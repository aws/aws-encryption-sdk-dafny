// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

// ReSharper disable thrice RedundantUsingDirective
using System;
using AWS.EncryptionSDK.Core;
using Wrappers_Compile;

namespace AWS.EncryptionSDK.Core
{
    public abstract class NativeWrapper_ClientSupplierBase : Dafny.Aws.EncryptionSdk.Core.IClientSupplier
    {
        internal readonly ClientSupplierBase _impl;

        internal NativeWrapper_ClientSupplierBase(ClientSupplierBase nativeImpl)
        {
            _impl = nativeImpl;
        }

        public abstract Wrappers_Compile._IResult<
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
        > GetClient(Dafny.Aws.EncryptionSdk.Core._IGetClientInput input);
    }
}
