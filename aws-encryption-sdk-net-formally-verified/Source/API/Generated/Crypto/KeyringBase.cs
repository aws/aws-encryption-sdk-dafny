// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public abstract class KeyringBase : IKeyring
    {
        public Aws.EncryptionSdk.Core.OnEncryptOutput OnEncrypt(Aws.EncryptionSdk.Core.OnEncryptInput input)
        {
            input.Validate();
            return _OnEncrypt(input);
        }

        protected abstract Aws.EncryptionSdk.Core.OnEncryptOutput _OnEncrypt(
            Aws.EncryptionSdk.Core.OnEncryptInput input);

        public Aws.EncryptionSdk.Core.OnDecryptOutput OnDecrypt(Aws.EncryptionSdk.Core.OnDecryptInput input)
        {
            input.Validate();
            return _OnDecrypt(input);
        }

        protected abstract Aws.EncryptionSdk.Core.OnDecryptOutput _OnDecrypt(
            Aws.EncryptionSdk.Core.OnDecryptInput input);
    }
}
