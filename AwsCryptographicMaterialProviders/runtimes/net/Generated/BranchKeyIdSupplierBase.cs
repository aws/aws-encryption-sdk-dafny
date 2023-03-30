// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public abstract class BranchKeyIdSupplierBase : IBranchKeyIdSupplier {
 public AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput GetBranchKeyId ( AWS.Cryptography.MaterialProviders.GetBranchKeyIdInput input )
 {
 input.Validate(); return _GetBranchKeyId ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput _GetBranchKeyId ( AWS.Cryptography.MaterialProviders.GetBranchKeyIdInput input ) ;
}
}
