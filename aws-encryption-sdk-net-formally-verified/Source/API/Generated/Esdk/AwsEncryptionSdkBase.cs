// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption
    ;

namespace Aws.Encryption
{
    public abstract class AwsEncryptionSdkBase : IAwsEncryptionSdk
    {
        public Aws.Encryption.EncryptOutput Encrypt(Aws.Encryption.EncryptInput input)
        {
            input.Validate();
            return _Encrypt(input);
        }

        protected abstract Aws.Encryption.EncryptOutput _Encrypt(Aws.Encryption.EncryptInput input);

        public Aws.Encryption.DecryptOutput Decrypt(Aws.Encryption.DecryptInput input)
        {
            input.Validate();
            return _Decrypt(input);
        }

        protected abstract Aws.Encryption.DecryptOutput _Decrypt(Aws.Encryption.DecryptInput input);
    }
}
