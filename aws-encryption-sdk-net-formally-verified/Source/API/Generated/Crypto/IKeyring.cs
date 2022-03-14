// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public interface IKeyring
    {
        Aws.Encryption.Core.OnEncryptOutput OnEncrypt(Aws.Encryption.Core.OnEncryptInput input);
        Aws.Encryption.Core.OnDecryptOutput OnDecrypt(Aws.Encryption.Core.OnDecryptInput input);
    }
}
