// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public interface ICryptoMaterialsCache
    {
        Aws.Crypto.PutEntryForEncryptOutput PutEntryForEncrypt(Aws.Crypto.PutEntryForEncryptInput input);
        Aws.Crypto.GetEntryForEncryptOutput GetEntryForEncrypt(Aws.Crypto.GetEntryForEncryptInput input);
        Aws.Crypto.PutEntryForDecryptOutput PutEntryForDecrypt(Aws.Crypto.PutEntryForDecryptInput input);
        Aws.Crypto.GetEntryForDecryptOutput GetEntryForDecrypt(Aws.Crypto.GetEntryForDecryptInput input);
        Aws.Crypto.DeleteEntryOutput DeleteEntry(Aws.Crypto.DeleteEntryInput input);
    }
}