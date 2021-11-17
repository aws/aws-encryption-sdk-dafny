// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    using Amazon.Runtime;

    public class CommitmentPolicy : ConstantClass
    {
        public static readonly CommitmentPolicy FORBID_ENCRYPT_ALLOW_DECRYPT =
            new CommitmentPolicy("FORBID_ENCRYPT_ALLOW_DECRYPT");

        public static readonly CommitmentPolicy REQUIRE_ENCRYPT_ALLOW_DECRYPT =
            new CommitmentPolicy("REQUIRE_ENCRYPT_ALLOW_DECRYPT");

        public static readonly CommitmentPolicy REQUIRE_ENCRYPT_REQUIRE_DECRYPT =
            new CommitmentPolicy("REQUIRE_ENCRYPT_REQUIRE_DECRYPT");

        public static readonly CommitmentPolicy[] Values =
        {
            FORBID_ENCRYPT_ALLOW_DECRYPT, REQUIRE_ENCRYPT_ALLOW_DECRYPT, REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        };

        public CommitmentPolicy(string value) : base(value)
        {
        }
    }
}