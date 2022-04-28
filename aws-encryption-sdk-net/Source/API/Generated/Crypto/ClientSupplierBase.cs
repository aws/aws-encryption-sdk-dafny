// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public abstract class ClientSupplierBase : IClientSupplier
    {
        public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(
            AWS.EncryptionSDK.Core.GetClientInput input)
        {
            input.Validate();
            return _GetClient(input);
        }

        protected abstract Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(
            AWS.EncryptionSDK.Core.GetClientInput input);
    }
}
