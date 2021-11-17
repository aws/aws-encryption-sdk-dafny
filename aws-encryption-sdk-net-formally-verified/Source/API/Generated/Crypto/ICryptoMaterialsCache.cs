// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public interface ICryptoMaterialsCache
    {
        PutEntryForEncryptOutput PutEntryForEncrypt(PutEntryForEncryptInput input);
        GetEntryForEncryptOutput GetEntryForEncrypt(GetEntryForEncryptInput input);
        PutEntryForDecryptOutput PutEntryForDecrypt(PutEntryForDecryptInput input);
        GetEntryForDecryptOutput GetEntryForDecrypt(GetEntryForDecryptInput input);
        DeleteEntryOutput DeleteEntry(DeleteEntryInput input);
    }
}