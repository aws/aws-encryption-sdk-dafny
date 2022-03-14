// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption
    ;

namespace Aws.Encryption
{
    public interface IAwsEncryptionSdk
    {
        Aws.Encryption.EncryptOutput Encrypt(Aws.Encryption.EncryptInput input);
        Aws.Encryption.DecryptOutput Decrypt(Aws.Encryption.DecryptInput input);
    }
}
