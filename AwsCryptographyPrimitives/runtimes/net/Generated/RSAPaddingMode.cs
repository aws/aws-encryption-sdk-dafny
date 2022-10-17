// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 using Amazon.Runtime; public class RSAPaddingMode : ConstantClass {

 
 public static readonly RSAPaddingMode PKCS1 = new RSAPaddingMode ("PKCS1");
 
 public static readonly RSAPaddingMode OAEP_SHA1 = new RSAPaddingMode ("OAEP_SHA1");
 
 public static readonly RSAPaddingMode OAEP_SHA256 = new RSAPaddingMode ("OAEP_SHA256");
 
 public static readonly RSAPaddingMode OAEP_SHA384 = new RSAPaddingMode ("OAEP_SHA384");
 
 public static readonly RSAPaddingMode OAEP_SHA512 = new RSAPaddingMode ("OAEP_SHA512");
 public static readonly  RSAPaddingMode [] Values =  {
 OAEP_SHA1 , OAEP_SHA256 , OAEP_SHA384 , OAEP_SHA512 , PKCS1
} ;
 public RSAPaddingMode (string value) : base(value) {}
}
}
