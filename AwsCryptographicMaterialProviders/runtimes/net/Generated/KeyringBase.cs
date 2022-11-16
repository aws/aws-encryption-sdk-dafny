// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public abstract class KeyringBase : IKeyring {
 public AWS.Cryptography.MaterialProviders.OnEncryptOutput OnEncrypt ( AWS.Cryptography.MaterialProviders.OnEncryptInput input )
 {
 input.Validate(); return _OnEncrypt ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.OnEncryptOutput _OnEncrypt ( AWS.Cryptography.MaterialProviders.OnEncryptInput input ) ;
 public AWS.Cryptography.MaterialProviders.OnDecryptOutput OnDecrypt ( AWS.Cryptography.MaterialProviders.OnDecryptInput input )
 {
 input.Validate(); return _OnDecrypt ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.OnDecryptOutput _OnDecrypt ( AWS.Cryptography.MaterialProviders.OnDecryptInput input ) ;
}
}
