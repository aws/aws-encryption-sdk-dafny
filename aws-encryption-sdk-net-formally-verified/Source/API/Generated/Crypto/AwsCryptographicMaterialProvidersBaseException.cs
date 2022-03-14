// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public class AwsCryptographicMaterialProvidersBaseException : Exception
    {
        public AwsCryptographicMaterialProvidersBaseException() : base()
        {
        }

        public AwsCryptographicMaterialProvidersBaseException(string message) : base(message)
        {
        }
    }
}
