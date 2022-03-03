// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class AwsCryptographicMaterialProvidersClientBase : IAwsCryptographicMaterialProviders
    {
        protected AwsCryptographicMaterialProvidersClientBase()
        {
        }

        public Aws.Crypto.IKeyring CreateAwsKmsKeyring(Aws.Crypto.CreateAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsKeyring(Aws.Crypto.CreateAwsKmsKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsDiscoveryKeyring(Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsMultiKeyring(Aws.Crypto.CreateAwsKmsMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring
            _CreateAwsKmsMultiKeyring(Aws.Crypto.CreateAwsKmsMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsMrkKeyring(Aws.Crypto.CreateAwsKmsMrkKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsMrkKeyring(Aws.Crypto.CreateAwsKmsMrkKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsMrkMultiKeyring(Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsMrkDiscoveryMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input)
        {
            input.Validate();
            return _CreateMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input);

        public Aws.Crypto.IKeyring CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input)
        {
            input.Validate();
            return _CreateRawRsaKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input);

        public Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input);

        public Aws.Crypto.IClientSupplier CreateDefaultClientSupplier(Aws.Crypto.CreateDefaultClientSupplierInput input)
        {
            input.Validate();
            return _CreateDefaultClientSupplier(input);
        }

        protected abstract Aws.Crypto.IClientSupplier _CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input);
    }
}
