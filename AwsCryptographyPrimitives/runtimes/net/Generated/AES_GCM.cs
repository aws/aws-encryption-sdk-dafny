// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class AES_GCM {
 private int? _keyLength ;
 private int? _tagLength ;
 private int? _ivLength ;
 public int KeyLength {
 get { return this._keyLength.GetValueOrDefault(); }
 set { this._keyLength = value; }
}
 internal bool IsSetKeyLength () {
 return this._keyLength.HasValue;
}
 public int TagLength {
 get { return this._tagLength.GetValueOrDefault(); }
 set { this._tagLength = value; }
}
 internal bool IsSetTagLength () {
 return this._tagLength.HasValue;
}
 public int IvLength {
 get { return this._ivLength.GetValueOrDefault(); }
 set { this._ivLength = value; }
}
 internal bool IsSetIvLength () {
 return this._ivLength.HasValue;
}
 public void Validate() {
 if (!IsSetKeyLength()) throw new System.ArgumentException("Missing value for required property 'KeyLength'");
 if (!IsSetTagLength()) throw new System.ArgumentException("Missing value for required property 'TagLength'");
 if (!IsSetIvLength()) throw new System.ArgumentException("Missing value for required property 'IvLength'");

}
}
}
