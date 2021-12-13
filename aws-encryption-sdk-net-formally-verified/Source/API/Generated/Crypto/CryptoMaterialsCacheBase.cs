// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class CryptoMaterialsCacheBase : ICryptoMaterialsCache
    {
        public Aws.Crypto.PutEntryForEncryptOutput PutEntryForEncrypt(Aws.Crypto.PutEntryForEncryptInput input)
        {
            input.Validate();
            return _PutEntryForEncrypt(input);
        }

        protected abstract Aws.Crypto.PutEntryForEncryptOutput _PutEntryForEncrypt(
            Aws.Crypto.PutEntryForEncryptInput input);

        public Aws.Crypto.GetEntryForEncryptOutput GetEntryForEncrypt(Aws.Crypto.GetEntryForEncryptInput input)
        {
            input.Validate();
            return _GetEntryForEncrypt(input);
        }

        protected abstract Aws.Crypto.GetEntryForEncryptOutput _GetEntryForEncrypt(
            Aws.Crypto.GetEntryForEncryptInput input);

        public Aws.Crypto.PutEntryForDecryptOutput PutEntryForDecrypt(Aws.Crypto.PutEntryForDecryptInput input)
        {
            input.Validate();
            return _PutEntryForDecrypt(input);
        }

        protected abstract Aws.Crypto.PutEntryForDecryptOutput _PutEntryForDecrypt(
            Aws.Crypto.PutEntryForDecryptInput input);

        public Aws.Crypto.GetEntryForDecryptOutput GetEntryForDecrypt(Aws.Crypto.GetEntryForDecryptInput input)
        {
            input.Validate();
            return _GetEntryForDecrypt(input);
        }

        protected abstract Aws.Crypto.GetEntryForDecryptOutput _GetEntryForDecrypt(
            Aws.Crypto.GetEntryForDecryptInput input);

        public Aws.Crypto.DeleteEntryOutput DeleteEntry(Aws.Crypto.DeleteEntryInput input)
        {
            input.Validate();
            return _DeleteEntry(input);
        }

        protected abstract Aws.Crypto.DeleteEntryOutput _DeleteEntry(Aws.Crypto.DeleteEntryInput input);
    }
}