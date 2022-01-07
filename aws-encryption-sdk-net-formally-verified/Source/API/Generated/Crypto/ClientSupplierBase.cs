// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class ClientSupplierBase : IClientSupplier
    {
        public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(Aws.Crypto.GetClientInput input)
        {
            input.Validate();
            return _GetClient(input);
        }

        protected abstract Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(
            Aws.Crypto.GetClientInput input);
    }
}
