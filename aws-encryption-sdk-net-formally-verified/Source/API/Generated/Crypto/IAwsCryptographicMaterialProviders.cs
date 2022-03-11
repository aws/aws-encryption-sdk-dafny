// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public interface IAwsCryptographicMaterialProviders {
 Aws.Crypto.IKeyring CreateAwsKmsKeyring ( Aws.Crypto.CreateAwsKmsKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsDiscoveryKeyring ( Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsMultiKeyring ( Aws.Crypto.CreateAwsKmsMultiKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsDiscoveryMultiKeyring ( Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsMrkKeyring ( Aws.Crypto.CreateAwsKmsMrkKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsMrkMultiKeyring ( Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsMrkDiscoveryKeyring ( Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring ( Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateMultiKeyring ( Aws.Crypto.CreateMultiKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateRawAesKeyring ( Aws.Crypto.CreateRawAesKeyringInput input ) ;
 Aws.Crypto.IKeyring CreateRawRsaKeyring ( Aws.Crypto.CreateRawRsaKeyringInput input ) ;
 Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager ( Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input ) ;
 Aws.Crypto.IClientSupplier CreateDefaultClientSupplier ( Aws.Crypto.CreateDefaultClientSupplierInput input ) ;
}
}
