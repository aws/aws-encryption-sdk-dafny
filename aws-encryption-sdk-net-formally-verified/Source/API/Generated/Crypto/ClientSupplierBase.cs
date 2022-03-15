// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public abstract class ClientSupplierBase : IClientSupplier
    {
        public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(
            Aws.EncryptionSdk.Core.GetClientInput input)
        {
            input.Validate();
            return _GetClient(input);
        }

        protected abstract Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(
            Aws.EncryptionSdk.Core.GetClientInput input);
    }
}
