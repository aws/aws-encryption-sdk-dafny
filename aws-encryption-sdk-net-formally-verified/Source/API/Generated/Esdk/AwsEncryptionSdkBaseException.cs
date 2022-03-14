// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption
    ;

namespace Aws.Encryption
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
