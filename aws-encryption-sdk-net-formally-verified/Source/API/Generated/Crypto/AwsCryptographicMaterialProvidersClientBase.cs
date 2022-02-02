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

        public Aws.Crypto.IKeyring CreateStrictAwsKmsKeyring(Aws.Crypto.CreateStrictAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateStrictAwsKmsKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateStrictAwsKmsKeyring(
            Aws.Crypto.CreateStrictAwsKmsKeyringInput input);

        public Aws.Crypto.IKeyring CreateAwsKmsDiscoveryKeyring(Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input)
        {
            input.Validate();
            return _CreateAwsKmsDiscoveryKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input);

        public Aws.Crypto.IKeyring CreateMrkAwareStrictAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateMrkAwareStrictAwsKmsKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateMrkAwareStrictAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input);

        public Aws.Crypto.IKeyring CreateMrkAwareStrictMultiKeyring(
            Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput input)
        {
            input.Validate();
            return _CreateMrkAwareStrictMultiKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateMrkAwareStrictMultiKeyring(
            Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput input);

        public Aws.Crypto.IKeyring CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input)
        {
            input.Validate();
            return _CreateMrkAwareDiscoveryAwsKmsKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input);

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

        public Aws.Crypto.CreateDefaultClientSupplierOutput CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input)
        {
            input.Validate();
            return _CreateDefaultClientSupplier(input);
        }

        protected abstract Aws.Crypto.CreateDefaultClientSupplierOutput _CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input);
    }
}