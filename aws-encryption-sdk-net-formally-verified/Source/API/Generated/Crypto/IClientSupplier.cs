// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public interface IClientSupplier
    {
        Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(Aws.EncryptionSdk.Core.GetClientInput input);
    }
}
