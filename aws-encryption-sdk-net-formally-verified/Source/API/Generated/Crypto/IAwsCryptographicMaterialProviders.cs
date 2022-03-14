// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public interface IAwsCryptographicMaterialProviders
    {
        Aws.Encryption.Core.IKeyring CreateAwsKmsKeyring(Aws.Encryption.Core.CreateAwsKmsKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsMultiKeyring(Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsMrkKeyring(Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        Aws.Encryption.Core.IKeyring CreateMultiKeyring(Aws.Encryption.Core.CreateMultiKeyringInput input);
        Aws.Encryption.Core.IKeyring CreateRawAesKeyring(Aws.Encryption.Core.CreateRawAesKeyringInput input);
        Aws.Encryption.Core.IKeyring CreateRawRsaKeyring(Aws.Encryption.Core.CreateRawRsaKeyringInput input);

        Aws.Encryption.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        Aws.Encryption.Core.IClientSupplier CreateDefaultClientSupplier(
            Aws.Encryption.Core.CreateDefaultClientSupplierInput input);
    }
}
