// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class AwsEncryptionSdkBaseException : Exception
    {
        public AwsEncryptionSdkBaseException() : base()
        {
        }

        public AwsEncryptionSdkBaseException(string message) : base(message)
        {
        }
    }
}
