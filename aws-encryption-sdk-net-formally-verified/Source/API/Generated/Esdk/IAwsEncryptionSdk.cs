// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:22:03.283903

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public interface IAwsEncryptionSdk
    {
        EncryptOutput Encrypt(EncryptInput input);
        DecryptOutput Decrypt(DecryptInput input);
    }
}
