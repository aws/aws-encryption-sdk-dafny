// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class RSAPrivateKey {
 private int? _lengthBits ;
 private System.IO.MemoryStream _pem ;
 public int LengthBits {
 get { return this._lengthBits.GetValueOrDefault(); }
 set { this._lengthBits = value; }
}
 public bool IsSetLengthBits () {
 return this._lengthBits.HasValue;
}
 public System.IO.MemoryStream Pem {
 get { return this._pem; }
 set { this._pem = value; }
}
 public bool IsSetPem () {
 return this._pem != null;
}
 public void Validate() {
 if (!IsSetLengthBits()) throw new System.ArgumentException("Missing value for required property 'LengthBits'");
 if (!IsSetPem()) throw new System.ArgumentException("Missing value for required property 'Pem'");

}
}
}
