// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public abstract class KeyringBase : IKeyring
    {
        public Aws.Encryption.Core.OnEncryptOutput OnEncrypt(Aws.Encryption.Core.OnEncryptInput input)
        {
            input.Validate();
            return _OnEncrypt(input);
        }

        protected abstract Aws.Encryption.Core.OnEncryptOutput _OnEncrypt(Aws.Encryption.Core.OnEncryptInput input);

        public Aws.Encryption.Core.OnDecryptOutput OnDecrypt(Aws.Encryption.Core.OnDecryptInput input)
        {
            input.Validate();
            return _OnDecrypt(input);
        }

        protected abstract Aws.Encryption.Core.OnDecryptOutput _OnDecrypt(Aws.Encryption.Core.OnDecryptInput input);
    }
}
