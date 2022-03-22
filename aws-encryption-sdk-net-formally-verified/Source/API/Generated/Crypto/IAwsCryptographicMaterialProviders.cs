// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public interface IAwsCryptographicMaterialProviders
    {
        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsKeyring(Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring
            CreateAwsKmsMrkKeyring(Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        Aws.EncryptionSdk.Core.IKeyring CreateMultiKeyring(Aws.EncryptionSdk.Core.CreateMultiKeyringInput input);
        Aws.EncryptionSdk.Core.IKeyring CreateRawAesKeyring(Aws.EncryptionSdk.Core.CreateRawAesKeyringInput input);
        Aws.EncryptionSdk.Core.IKeyring CreateRawRsaKeyring(Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput input);

        Aws.EncryptionSdk.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        Aws.EncryptionSdk.Core.IClientSupplier CreateDefaultClientSupplier(
            Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput input);
    }
}
