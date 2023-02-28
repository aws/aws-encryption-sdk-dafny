// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class KdfCtrInput {
 private AWS.Cryptography.Primitives.DigestAlgorithm _digestAlgorithm ;
 private System.IO.MemoryStream _ikm ;
 private int? _expectedLength ;
 private System.IO.MemoryStream _purpose ;
 private System.IO.MemoryStream _nonce ;
 public AWS.Cryptography.Primitives.DigestAlgorithm DigestAlgorithm {
 get { return this._digestAlgorithm; }
 set { this._digestAlgorithm = value; }
}
 public bool IsSetDigestAlgorithm () {
 return this._digestAlgorithm != null;
}
 public System.IO.MemoryStream Ikm {
 get { return this._ikm; }
 set { this._ikm = value; }
}
 public bool IsSetIkm () {
 return this._ikm != null;
}
 public int ExpectedLength {
 get { return this._expectedLength.GetValueOrDefault(); }
 set { this._expectedLength = value; }
}
 public bool IsSetExpectedLength () {
 return this._expectedLength.HasValue;
}
 public System.IO.MemoryStream Purpose {
 get { return this._purpose; }
 set { this._purpose = value; }
}
 public bool IsSetPurpose () {
 return this._purpose != null;
}
 public System.IO.MemoryStream Nonce {
 get { return this._nonce; }
 set { this._nonce = value; }
}
 public bool IsSetNonce () {
 return this._nonce != null;
}
 public void Validate() {
 if (!IsSetDigestAlgorithm()) throw new System.ArgumentException("Missing value for required property 'DigestAlgorithm'");
 if (!IsSetIkm()) throw new System.ArgumentException("Missing value for required property 'Ikm'");
 if (!IsSetExpectedLength()) throw new System.ArgumentException("Missing value for required property 'ExpectedLength'");

}
}
}
