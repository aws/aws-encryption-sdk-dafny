// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:32:59.305823

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public abstract class AwsEncryptionSdkClientBase : IAwsEncryptionSdk
    {
        protected AwsEncryptionSdkClientBase()
        {
        }

        public EncryptOutput Encrypt(EncryptInput input)
        {
            input.Validate();
            return _Encrypt(input);
        }

        protected abstract EncryptOutput _Encrypt(EncryptInput input);

        public DecryptOutput Decrypt(DecryptInput input)
        {
            input.Validate();
            return _Decrypt(input);
        }

        protected abstract DecryptOutput _Decrypt(DecryptInput input);
    }
}