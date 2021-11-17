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
    public interface IAwsEncryptionSdk
    {
        EncryptOutput Encrypt(EncryptInput input);
        DecryptOutput Decrypt(DecryptInput input);
    }
}