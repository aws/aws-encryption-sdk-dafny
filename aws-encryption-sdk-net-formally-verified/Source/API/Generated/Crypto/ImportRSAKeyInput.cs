// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class ImportRSAKeyInput
    {
        private string _pem;
        private long? _strength;
        private Aws.Crypto.PaddingScheme _paddingScheme;

        public string Pem
        {
            get { return this._pem; }
            set { this._pem = value; }
        }

        public long Strength
        {
            get { return this._strength.GetValueOrDefault(); }
            set { this._strength = value; }
        }

        public Aws.Crypto.PaddingScheme PaddingScheme
        {
            get { return this._paddingScheme; }
            set { this._paddingScheme = value; }
        }

        public void Validate()
        {
        }
    }
}