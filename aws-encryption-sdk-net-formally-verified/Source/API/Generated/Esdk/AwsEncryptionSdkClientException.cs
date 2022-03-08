// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class AwsEncryptionSdkClientException : AwsEncryptionSdkClientFactoryException
    {
        public AwsEncryptionSdkClientException(string message) : base(message)
        {
        }
    }
}
