// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using Amazon.KeyManagementService;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public abstract class ClientSupplierBase : IClientSupplier
    {
        public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(
            AWS.EncryptionSDK.Core.GetClientInput input)
        {
            input.Validate();
            var output = _GetClient(input);
            _ = output ?? throw new ArgumentNullException(
                $"Output of {this}._GetClient is invalid. Should be {typeof(IAmazonKeyManagementService)} but is {null}.");
            return output;
        }

        protected abstract Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(
            AWS.EncryptionSDK.Core.GetClientInput input);
    }
}
