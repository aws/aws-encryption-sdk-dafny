// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public abstract class ClientSupplierBase : IClientSupplier {
 public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient ( AWS.Cryptography.MaterialProviders.GetClientInput input )
 {
 input.Validate(); return _GetClient ( input ) ;
}
 protected abstract Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient ( AWS.Cryptography.MaterialProviders.GetClientInput input ) ;
}
}
