// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 using Amazon.Runtime; public class DigestAlgorithm : ConstantClass {

 
 public static readonly DigestAlgorithm SHA_512 = new DigestAlgorithm ("SHA_512");
 
 public static readonly DigestAlgorithm SHA_384 = new DigestAlgorithm ("SHA_384");
 
 public static readonly DigestAlgorithm SHA_256 = new DigestAlgorithm ("SHA_256");
 public static readonly  DigestAlgorithm [] Values =  {
 SHA_256 , SHA_384 , SHA_512
} ;
 public DigestAlgorithm (string value) : base(value) {}
}
}
