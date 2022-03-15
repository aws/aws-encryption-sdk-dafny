// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
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
