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
    internal class PublicKey : PublicKeyBase
    {
        internal Dafny.Aws.Crypto.IPublicKey _impl { get; }

        internal PublicKey(Dafny.Aws.Crypto.IPublicKey impl)
        {
            this._impl = impl;
        }
    }
}