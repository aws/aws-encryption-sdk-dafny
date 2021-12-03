// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    using Amazon.Runtime;

    public class AlgorithmSuiteId : ConstantClass
    {
        public static readonly AlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_NO_KDF = new AlgorithmSuiteId("0x0014");

        public static readonly AlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_NO_KDF = new AlgorithmSuiteId("0x0046");

        public static readonly AlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_NO_KDF = new AlgorithmSuiteId("0x0078");

        public static readonly AlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 = new AlgorithmSuiteId("0x0114");

        public static readonly AlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 = new AlgorithmSuiteId("0x0146");

        public static readonly AlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 = new AlgorithmSuiteId("0x0178");

        public static readonly AlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 =
            new AlgorithmSuiteId("0x0214");

        public static readonly AlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 =
            new AlgorithmSuiteId("0x0346");

        public static readonly AlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 =
            new AlgorithmSuiteId("0x0378");

        public static readonly AlgorithmSuiteId[] Values =
        {
            ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256, ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
            ALG_AES_128_GCM_IV12_TAG16_NO_KDF, ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
            ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
            ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256, ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
            ALG_AES_256_GCM_IV12_TAG16_NO_KDF
        };

        public AlgorithmSuiteId(string value) : base(value)
        {
        }
    }
}
