// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public abstract class AwsEncryptionSdkFactoryClientBase : IAwsEncryptionSdkFactory
    {
        protected AwsEncryptionSdkFactoryClientBase()
        {
        }

        public Aws.Esdk.IAwsEncryptionSdkClient MakeAwsEncryptionSdk(Aws.Esdk.AwsEncryptionSdkClientConfig input)
        {
            input.Validate();
            return _MakeAwsEncryptionSdk(input);
        }

        protected abstract Aws.Esdk.IAwsEncryptionSdkClient _MakeAwsEncryptionSdk(
            Aws.Esdk.AwsEncryptionSdkClientConfig input);
    }
}
