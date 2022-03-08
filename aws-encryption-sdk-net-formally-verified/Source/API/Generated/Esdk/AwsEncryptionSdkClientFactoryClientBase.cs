// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public abstract class AwsEncryptionSdkClientFactoryClientBase : IAwsEncryptionSdkClientFactory
    {
        protected AwsEncryptionSdkClientFactoryClientBase()
        {
        }

        public Aws.Esdk.IAwsEncryptionSdkClient MakeAwsEncryptionSdkClient(Aws.Esdk.AwsEncryptionSdkClientConfig input)
        {
            input.Validate();
            return _MakeAwsEncryptionSdkClient(input);
        }

        protected abstract Aws.Esdk.IAwsEncryptionSdkClient _MakeAwsEncryptionSdkClient(
            Aws.Esdk.AwsEncryptionSdkClientConfig input);
    }
}
