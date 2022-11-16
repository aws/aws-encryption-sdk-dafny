// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 using Amazon.Runtime; public class ESDKCommitmentPolicy : ConstantClass {

 
 public static readonly ESDKCommitmentPolicy FORBID_ENCRYPT_ALLOW_DECRYPT = new ESDKCommitmentPolicy ("FORBID_ENCRYPT_ALLOW_DECRYPT");
 
 public static readonly ESDKCommitmentPolicy REQUIRE_ENCRYPT_ALLOW_DECRYPT = new ESDKCommitmentPolicy ("REQUIRE_ENCRYPT_ALLOW_DECRYPT");
 
 public static readonly ESDKCommitmentPolicy REQUIRE_ENCRYPT_REQUIRE_DECRYPT = new ESDKCommitmentPolicy ("REQUIRE_ENCRYPT_REQUIRE_DECRYPT");
 public static readonly  ESDKCommitmentPolicy [] Values =  {
 FORBID_ENCRYPT_ALLOW_DECRYPT , REQUIRE_ENCRYPT_ALLOW_DECRYPT , REQUIRE_ENCRYPT_REQUIRE_DECRYPT
} ;
 public ESDKCommitmentPolicy (string value) : base(value) {}
}
}
