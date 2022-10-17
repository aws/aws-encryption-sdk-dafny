// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 using Amazon.Runtime; public class SignatureAlgorithm : ConstantClass {

 
 public static readonly SignatureAlgorithm ECDSA_P384 = new SignatureAlgorithm ("ECDSA_P384");
 
 public static readonly SignatureAlgorithm ECDSA_P256 = new SignatureAlgorithm ("ECDSA_P256");
 public static readonly  SignatureAlgorithm [] Values =  {
 ECDSA_P256 , ECDSA_P384
} ;
 public SignatureAlgorithm (string value) : base(value) {}
}
}
