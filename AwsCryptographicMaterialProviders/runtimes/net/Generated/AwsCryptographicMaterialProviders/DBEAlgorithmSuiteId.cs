// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 using Amazon.Runtime; public class DBEAlgorithmSuiteId : ConstantClass {

 
 public static readonly DBEAlgorithmSuiteId ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384 = new DBEAlgorithmSuiteId ("0x6700");
 
 public static readonly DBEAlgorithmSuiteId ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384 = new DBEAlgorithmSuiteId ("0x6701");
 public static readonly  DBEAlgorithmSuiteId [] Values =  {
 ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384 , ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384
} ;
 public DBEAlgorithmSuiteId (string value) : base(value) {}
}
}
