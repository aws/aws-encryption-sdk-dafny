// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public interface IClientSupplier
    {
        Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(Aws.Crypto.GetClientInput input);
    }
}
