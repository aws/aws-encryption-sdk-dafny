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
    public abstract class CryptoMaterialsCacheBase : ICryptoMaterialsCache
    {
        public PutEntryForEncryptOutput PutEntryForEncrypt(PutEntryForEncryptInput input)
        {
            input.Validate();
            return _PutEntryForEncrypt(input);
        }

        protected abstract PutEntryForEncryptOutput _PutEntryForEncrypt(PutEntryForEncryptInput input);

        public GetEntryForEncryptOutput GetEntryForEncrypt(GetEntryForEncryptInput input)
        {
            input.Validate();
            return _GetEntryForEncrypt(input);
        }

        protected abstract GetEntryForEncryptOutput _GetEntryForEncrypt(GetEntryForEncryptInput input);

        public PutEntryForDecryptOutput PutEntryForDecrypt(PutEntryForDecryptInput input)
        {
            input.Validate();
            return _PutEntryForDecrypt(input);
        }

        protected abstract PutEntryForDecryptOutput _PutEntryForDecrypt(PutEntryForDecryptInput input);

        public GetEntryForDecryptOutput GetEntryForDecrypt(GetEntryForDecryptInput input)
        {
            input.Validate();
            return _GetEntryForDecrypt(input);
        }

        protected abstract GetEntryForDecryptOutput _GetEntryForDecrypt(GetEntryForDecryptInput input);

        public DeleteEntryOutput DeleteEntry(DeleteEntryInput input)
        {
            input.Validate();
            return _DeleteEntry(input);
        }

        protected abstract DeleteEntryOutput _DeleteEntry(DeleteEntryInput input);
    }
}