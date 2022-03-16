// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk
    ;

namespace Aws.EncryptionSdk
{
    public class AwsEncryptionSdkException : AwsEncryptionSdkBaseException
    {
        public AwsEncryptionSdkException(string message) : base(message)
        {
        }
    }
}
