// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public abstract class AwsCryptographicMaterialProvidersBase : IAwsCryptographicMaterialProviders
    {
        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMultiKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkMultiKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateMultiKeyring(Aws.EncryptionSdk.Core.CreateMultiKeyringInput input)
        {
            input.Validate();
            return _CreateMultiKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateMultiKeyring(
            Aws.EncryptionSdk.Core.CreateMultiKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateRawAesKeyring(
            Aws.EncryptionSdk.Core.CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateRawAesKeyring(
            Aws.EncryptionSdk.Core.CreateRawAesKeyringInput input);

        public Aws.EncryptionSdk.Core.IKeyring CreateRawRsaKeyring(
            Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput input)
        {
            input.Validate();
            return _CreateRawRsaKeyring(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IKeyring _CreateRawRsaKeyring(
            Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput input);

        public Aws.EncryptionSdk.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            _CreateDefaultCryptographicMaterialsManager(
                Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        public Aws.EncryptionSdk.Core.IClientSupplier CreateDefaultClientSupplier(
            Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput input)
        {
            input.Validate();
            return _CreateDefaultClientSupplier(input);
        }

        protected abstract Aws.EncryptionSdk.Core.IClientSupplier _CreateDefaultClientSupplier(
            Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput input);
    }
}
