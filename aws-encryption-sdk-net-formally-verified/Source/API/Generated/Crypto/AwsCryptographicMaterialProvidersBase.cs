// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public abstract class AwsCryptographicMaterialProvidersBase : IAwsCryptographicMaterialProviders
    {
        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMultiKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryMultiKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsMrkKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkMultiKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsMrkMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryMultiKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateMultiKeyring(AWS.EncryptionSDK.Core.CreateMultiKeyringInput input)
        {
            input.Validate();
            return _CreateMultiKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateMultiKeyring(
            AWS.EncryptionSDK.Core.CreateMultiKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateRawAesKeyring(
            AWS.EncryptionSDK.Core.CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateRawAesKeyring(
            AWS.EncryptionSDK.Core.CreateRawAesKeyringInput input);

        public AWS.EncryptionSDK.Core.IKeyring CreateRawRsaKeyring(
            AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput input)
        {
            input.Validate();
            return _CreateRawRsaKeyring(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IKeyring _CreateRawRsaKeyring(
            AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput input);

        public AWS.EncryptionSDK.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract AWS.EncryptionSDK.Core.ICryptographicMaterialsManager
            _CreateDefaultCryptographicMaterialsManager(
                AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        public AWS.EncryptionSDK.Core.IClientSupplier CreateDefaultClientSupplier(
            AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput input)
        {
            input.Validate();
            return _CreateDefaultClientSupplier(input);
        }

        protected abstract AWS.EncryptionSDK.Core.IClientSupplier _CreateDefaultClientSupplier(
            AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput input);
    }
}
