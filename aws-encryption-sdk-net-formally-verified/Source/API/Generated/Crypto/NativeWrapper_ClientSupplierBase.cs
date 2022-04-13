// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

// ReSharper disable once RedundantUsingDirective
using AWS.EncryptionSDK.Core;

// ReSharper disable once RedundantUsingDirective
using Wrappers_Compile;

namespace AWS.EncryptionSDK.Core
{
    public abstract class NativeWrapper_ClientSupplierBase : Dafny.Aws.EncryptionSdk.Core.IClientSupplier
    {
        public IClientSupplier _impl;

        public abstract _IResult<
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
        > GetClient(Dafny.Aws.EncryptionSdk.Core._IGetClientInput input);
    }
}
