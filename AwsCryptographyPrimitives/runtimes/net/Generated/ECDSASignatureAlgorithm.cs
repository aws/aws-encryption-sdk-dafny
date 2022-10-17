// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 using Amazon.Runtime; public class ECDSASignatureAlgorithm : ConstantClass {

 
 public static readonly ECDSASignatureAlgorithm ECDSA_P384 = new ECDSASignatureAlgorithm ("ECDSA_P384");
 
 public static readonly ECDSASignatureAlgorithm ECDSA_P256 = new ECDSASignatureAlgorithm ("ECDSA_P256");
 public static readonly  ECDSASignatureAlgorithm [] Values =  {
 ECDSA_P256 , ECDSA_P384
} ;
 public ECDSASignatureAlgorithm (string value) : base(value) {}
}
}
