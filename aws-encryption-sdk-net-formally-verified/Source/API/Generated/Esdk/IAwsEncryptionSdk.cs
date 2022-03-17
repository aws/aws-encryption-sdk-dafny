// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk
    ;

namespace Aws.EncryptionSdk
{
    public interface IAwsEncryptionSdk
    {
        Aws.EncryptionSdk.EncryptOutput Encrypt(Aws.EncryptionSdk.EncryptInput input);
        Aws.EncryptionSdk.DecryptOutput Decrypt(Aws.EncryptionSdk.DecryptInput input);
    }
}
