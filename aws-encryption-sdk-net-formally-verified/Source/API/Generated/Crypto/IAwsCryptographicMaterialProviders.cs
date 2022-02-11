// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public interface IAwsCryptographicMaterialProviders
    {
        Aws.Crypto.IKeyring CreateStrictAwsKmsKeyring(Aws.Crypto.CreateStrictAwsKmsKeyringInput input);
        Aws.Crypto.IKeyring CreateAwsKmsDiscoveryKeyring(Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input);
        Aws.Crypto.IKeyring CreateStrictAwsKmsMultiKeyring(Aws.Crypto.CreateStrictAwsKmsMultiKeyringInput input);
        Aws.Crypto.IKeyring CreateAwsKmsDiscoveryMultiKeyring(Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input);
        Aws.Crypto.IKeyring CreateMrkAwareStrictAwsKmsKeyring(Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input);
        Aws.Crypto.IKeyring CreateMrkAwareStrictMultiKeyring(Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput input);

        Aws.Crypto.IKeyring CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input);

        Aws.Crypto.IKeyring CreateMrkAwareDiscoveryMultiKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput input);

        Aws.Crypto.IKeyring CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input);
        Aws.Crypto.IKeyring CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input);
        Aws.Crypto.IKeyring CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input);

        Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input);

        Aws.Crypto.IClientSupplier CreateDefaultClientSupplier(Aws.Crypto.CreateDefaultClientSupplierInput input);
    }
}
