// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public interface ICryptographicMaterialsManager {
 AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput GetEncryptionMaterials ( AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsInput input ) ;
 AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput DecryptMaterials ( AWS.Cryptography.MaterialProviders.DecryptMaterialsInput input ) ;
}
}
