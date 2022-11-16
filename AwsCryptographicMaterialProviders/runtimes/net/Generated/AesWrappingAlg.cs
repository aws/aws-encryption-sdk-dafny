// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 using Amazon.Runtime; public class AesWrappingAlg : ConstantClass {

 
 public static readonly AesWrappingAlg ALG_AES128_GCM_IV12_TAG16 = new AesWrappingAlg ("ALG_AES128_GCM_IV12_TAG16");
 
 public static readonly AesWrappingAlg ALG_AES192_GCM_IV12_TAG16 = new AesWrappingAlg ("ALG_AES192_GCM_IV12_TAG16");
 
 public static readonly AesWrappingAlg ALG_AES256_GCM_IV12_TAG16 = new AesWrappingAlg ("ALG_AES256_GCM_IV12_TAG16");
 public static readonly  AesWrappingAlg [] Values =  {
 ALG_AES128_GCM_IV12_TAG16 , ALG_AES192_GCM_IV12_TAG16 , ALG_AES256_GCM_IV12_TAG16
} ;
 public AesWrappingAlg (string value) : base(value) {}
}
}
