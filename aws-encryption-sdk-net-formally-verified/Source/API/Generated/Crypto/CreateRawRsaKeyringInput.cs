// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateRawRsaKeyringInput
    {
        private string _keyNamespace;
        private string _keyName;
        private Aws.Crypto.PaddingScheme _paddingScheme;
        private Aws.Crypto.IKey _publicKey;
        private Aws.Crypto.IKey _privateKey;

        public string KeyNamespace
        {
            get { return this._keyNamespace; }
            set { this._keyNamespace = value; }
        }

        public string KeyName
        {
            get { return this._keyName; }
            set { this._keyName = value; }
        }

        public Aws.Crypto.PaddingScheme PaddingScheme
        {
            get { return this._paddingScheme; }
            set { this._paddingScheme = value; }
        }

        public Aws.Crypto.IKey PublicKey
        {
            get { return this._publicKey; }
            set { this._publicKey = value; }
        }

        public Aws.Crypto.IKey PrivateKey
        {
            get { return this._privateKey; }
            set { this._privateKey = value; }
        }

        public void Validate()
        {
        }
    }
}