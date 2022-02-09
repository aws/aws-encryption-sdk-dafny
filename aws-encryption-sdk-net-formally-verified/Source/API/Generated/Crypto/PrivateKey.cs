// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    internal class PrivateKey : PrivateKeyBase
    {
        internal Dafny.Aws.Crypto.IPrivateKey _impl { get; }

        internal PrivateKey(Dafny.Aws.Crypto.IPrivateKey impl)
        {
            this._impl = impl;
        }
    }
}