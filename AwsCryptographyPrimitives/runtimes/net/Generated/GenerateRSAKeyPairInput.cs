// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GenerateRSAKeyPairInput {
 private int? _lengthBits ;
 public int LengthBits {
 get { return this._lengthBits.GetValueOrDefault(); }
 set { this._lengthBits = value; }
}
 public bool IsSetLengthBits () {
 return this._lengthBits.HasValue;
}
 public void Validate() {
 if (!IsSetLengthBits()) throw new System.ArgumentException("Missing value for required property 'LengthBits'");

}
}
}
