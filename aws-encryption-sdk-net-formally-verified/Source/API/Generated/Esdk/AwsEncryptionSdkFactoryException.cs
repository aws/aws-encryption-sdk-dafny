// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class AwsEncryptionSdkFactoryException : Exception
    {
        public AwsEncryptionSdkFactoryException() : base()
        {
        }

        public AwsEncryptionSdkFactoryException(string message) : base(message)
        {
        }
    }
}
