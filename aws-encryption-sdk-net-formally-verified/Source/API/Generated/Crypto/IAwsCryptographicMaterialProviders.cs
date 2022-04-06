// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public interface IAwsCryptographicMaterialProviders
    {
        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsKeyring(AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring
            CreateAwsKmsMrkKeyring(AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        AWS.EncryptionSDK.Core.IKeyring CreateMultiKeyring(AWS.EncryptionSDK.Core.CreateMultiKeyringInput input);
        AWS.EncryptionSDK.Core.IKeyring CreateRawAesKeyring(AWS.EncryptionSDK.Core.CreateRawAesKeyringInput input);
        AWS.EncryptionSDK.Core.IKeyring CreateRawRsaKeyring(AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput input);

        AWS.EncryptionSDK.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        AWS.EncryptionSDK.Core.IClientSupplier CreateDefaultClientSupplier(
            AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput input);
    }
}
