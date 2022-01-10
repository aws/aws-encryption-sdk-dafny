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
        Aws.Crypto.IKeyring CreateAwsKmsDiscoveryKeyring(Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input);
        Aws.Crypto.IKeyring CreateMrkAwareStrictAwsKmsKeyring(Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input);

        Aws.Crypto.IKeyring CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input);

        Aws.Crypto.IKeyring CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input);
        Aws.Crypto.IKeyring CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input);

        Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input);
    }
}
