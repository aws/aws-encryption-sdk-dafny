// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public interface IAwsEncryptionSdk
    {
        Aws.Esdk.EncryptOutput Encrypt(Aws.Esdk.EncryptInput input);
        Aws.Esdk.DecryptOutput Decrypt(Aws.Esdk.DecryptInput input);
    }
}