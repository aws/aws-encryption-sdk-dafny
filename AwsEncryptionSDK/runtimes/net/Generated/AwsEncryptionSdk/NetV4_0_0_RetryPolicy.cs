// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.EncryptionSDK;
namespace AWS.Cryptography.EncryptionSDK
{
    using Amazon.Runtime;
    public class NetV4_0_0_RetryPolicy : ConstantClass
    {


        public static readonly NetV4_0_0_RetryPolicy FORBID_RETRY = new NetV4_0_0_RetryPolicy("FORBID_RETRY");

        public static readonly NetV4_0_0_RetryPolicy ALLOW_RETRY = new NetV4_0_0_RetryPolicy("ALLOW_RETRY");
        public static readonly NetV4_0_0_RetryPolicy[] Values =  {
 ALLOW_RETRY , FORBID_RETRY
};
        public NetV4_0_0_RetryPolicy(string value) : base(value) { }
    }
}
