// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class AES_CTR {
 private int? _keyLength ;
 private int? _nonceLength ;
 public int KeyLength {
 get { return this._keyLength.GetValueOrDefault(); }
 set { this._keyLength = value; }
}
 public bool IsSetKeyLength () {
 return this._keyLength.HasValue;
}
 public int NonceLength {
 get { return this._nonceLength.GetValueOrDefault(); }
 set { this._nonceLength = value; }
}
 public bool IsSetNonceLength () {
 return this._nonceLength.HasValue;
}
 public void Validate() {
 if (!IsSetKeyLength()) throw new System.ArgumentException("Missing value for required property 'KeyLength'");
 if (!IsSetNonceLength()) throw new System.ArgumentException("Missing value for required property 'NonceLength'");

}
}
}
