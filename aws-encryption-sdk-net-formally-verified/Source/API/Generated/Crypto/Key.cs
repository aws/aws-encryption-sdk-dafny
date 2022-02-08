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
    internal class Key : KeyBase
    {
        internal Dafny.Aws.Crypto.IKey _impl { get; }

        internal Key(Dafny.Aws.Crypto.IKey impl)
        {
            this._impl = impl;
        }
    }
}
