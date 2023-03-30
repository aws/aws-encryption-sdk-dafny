// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 using Amazon.Runtime; public class DBECommitmentPolicy : ConstantClass {

 
 public static readonly DBECommitmentPolicy REQUIRE_ENCRYPT_REQUIRE_DECRYPT = new DBECommitmentPolicy ("REQUIRE_ENCRYPT_REQUIRE_DECRYPT");
 public static readonly  DBECommitmentPolicy [] Values =  {
 REQUIRE_ENCRYPT_REQUIRE_DECRYPT
} ;
 public DBECommitmentPolicy (string value) : base(value) {}
}
}
