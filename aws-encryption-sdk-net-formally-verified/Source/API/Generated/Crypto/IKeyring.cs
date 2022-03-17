// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public interface IKeyring
    {
        Aws.EncryptionSdk.Core.OnEncryptOutput OnEncrypt(Aws.EncryptionSdk.Core.OnEncryptInput input);
        Aws.EncryptionSdk.Core.OnDecryptOutput OnDecrypt(Aws.EncryptionSdk.Core.OnDecryptInput input);
    }
}
