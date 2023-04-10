// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager {
 public AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput GetEncryptionMaterials ( AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsInput input )
 {
 input.Validate(); return _GetEncryptionMaterials ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput _GetEncryptionMaterials ( AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsInput input ) ;
 public AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput DecryptMaterials ( AWS.Cryptography.MaterialProviders.DecryptMaterialsInput input )
 {
 input.Validate(); return _DecryptMaterials ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput _DecryptMaterials ( AWS.Cryptography.MaterialProviders.DecryptMaterialsInput input ) ;
}
}
