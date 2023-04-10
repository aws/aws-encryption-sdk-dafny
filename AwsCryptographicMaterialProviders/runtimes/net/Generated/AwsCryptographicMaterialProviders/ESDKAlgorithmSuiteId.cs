// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 using Amazon.Runtime; public class ESDKAlgorithmSuiteId : ConstantClass {

 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_NO_KDF = new ESDKAlgorithmSuiteId ("0x0014");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_NO_KDF = new ESDKAlgorithmSuiteId ("0x0046");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_NO_KDF = new ESDKAlgorithmSuiteId ("0x0078");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 = new ESDKAlgorithmSuiteId ("0x0114");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 = new ESDKAlgorithmSuiteId ("0x0146");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 = new ESDKAlgorithmSuiteId ("0x0178");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 = new ESDKAlgorithmSuiteId ("0x0214");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 = new ESDKAlgorithmSuiteId ("0x0346");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 = new ESDKAlgorithmSuiteId ("0x0378");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY = new ESDKAlgorithmSuiteId ("0x0478");
 
 public static readonly ESDKAlgorithmSuiteId ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 = new ESDKAlgorithmSuiteId ("0x0578");
 public static readonly  ESDKAlgorithmSuiteId [] Values =  {
 ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 , ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 , ALG_AES_128_GCM_IV12_TAG16_NO_KDF , ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 , ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 , ALG_AES_192_GCM_IV12_TAG16_NO_KDF , ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY , ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 , ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 , ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 , ALG_AES_256_GCM_IV12_TAG16_NO_KDF
} ;
 public ESDKAlgorithmSuiteId (string value) : base(value) {}
}
}
