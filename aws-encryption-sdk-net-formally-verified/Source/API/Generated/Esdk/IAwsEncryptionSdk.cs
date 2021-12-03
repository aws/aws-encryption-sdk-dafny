// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:12:30.370597

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
