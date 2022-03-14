// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public abstract class AwsCryptographicMaterialProvidersBase : IAwsCryptographicMaterialProviders
    {
        public Aws.Encryption.Core.IKeyring CreateAwsKmsKeyring(Aws.Encryption.Core.CreateAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsKeyring(
            Aws.Encryption.Core.CreateAwsKmsKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMultiKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsMrkKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsMrkMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkMultiKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateMultiKeyring(Aws.Encryption.Core.CreateMultiKeyringInput input)
        {
            input.Validate();
            return _CreateMultiKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateMultiKeyring(
            Aws.Encryption.Core.CreateMultiKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateRawAesKeyring(Aws.Encryption.Core.CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateRawAesKeyring(
            Aws.Encryption.Core.CreateRawAesKeyringInput input);

        public Aws.Encryption.Core.IKeyring CreateRawRsaKeyring(Aws.Encryption.Core.CreateRawRsaKeyringInput input)
        {
            input.Validate();
            return _CreateRawRsaKeyring(input);
        }

        protected abstract Aws.Encryption.Core.IKeyring _CreateRawRsaKeyring(
            Aws.Encryption.Core.CreateRawRsaKeyringInput input);

        public Aws.Encryption.Core.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract Aws.Encryption.Core.ICryptographicMaterialsManager
            _CreateDefaultCryptographicMaterialsManager(
                Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput input);

        public Aws.Encryption.Core.IClientSupplier CreateDefaultClientSupplier(
            Aws.Encryption.Core.CreateDefaultClientSupplierInput input)
        {
            input.Validate();
            return _CreateDefaultClientSupplier(input);
        }

        protected abstract Aws.Encryption.Core.IClientSupplier _CreateDefaultClientSupplier(
            Aws.Encryption.Core.CreateDefaultClientSupplierInput input);
    }
}
