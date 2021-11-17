// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class KeyringBase : IKeyring
    {
        public OnEncryptOutput OnEncrypt(OnEncryptInput input)
        {
            input.Validate();
            return _OnEncrypt(input);
        }

        protected abstract OnEncryptOutput _OnEncrypt(OnEncryptInput input);

        public OnDecryptOutput OnDecrypt(OnDecryptInput input)
        {
            input.Validate();
            return _OnDecrypt(input);
        }

        protected abstract OnDecryptOutput _OnDecrypt(OnDecryptInput input);
    }
}