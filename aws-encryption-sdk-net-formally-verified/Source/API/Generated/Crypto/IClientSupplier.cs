// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public interface IClientSupplier
    {
        Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(Aws.Encryption.Core.GetClientInput input);
    }
}
