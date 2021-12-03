// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:30:30.159384

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class KeyringBase : IKeyring
    {
        public Aws.Crypto.OnEncryptOutput OnEncrypt(Aws.Crypto.OnEncryptInput input)
        {
            input.Validate();
            return _OnEncrypt(input);
        }

        protected abstract Aws.Crypto.OnEncryptOutput _OnEncrypt(Aws.Crypto.OnEncryptInput input);

        public Aws.Crypto.OnDecryptOutput OnDecrypt(Aws.Crypto.OnDecryptInput input)
        {
            input.Validate();
            return _OnDecrypt(input);
        }

        protected abstract Aws.Crypto.OnDecryptOutput _OnDecrypt(Aws.Crypto.OnDecryptInput input);
    }
}
