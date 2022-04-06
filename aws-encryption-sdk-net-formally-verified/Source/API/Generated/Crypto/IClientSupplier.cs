// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public interface IClientSupplier
    {
        Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(AWS.EncryptionSDK.Core.GetClientInput input);
    }
}
