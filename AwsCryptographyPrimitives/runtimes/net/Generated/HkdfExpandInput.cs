// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class HkdfExpandInput {
 private AWS.Cryptography.Primitives.DigestAlgorithm _digestAlgorithm ;
 private System.IO.MemoryStream _prk ;
 private System.IO.MemoryStream _info ;
 private int? _expectedLength ;
 public AWS.Cryptography.Primitives.DigestAlgorithm DigestAlgorithm {
 get { return this._digestAlgorithm; }
 set { this._digestAlgorithm = value; }
}
 public bool IsSetDigestAlgorithm () {
 return this._digestAlgorithm != null;
}
 public System.IO.MemoryStream Prk {
 get { return this._prk; }
 set { this._prk = value; }
}
 public bool IsSetPrk () {
 return this._prk != null;
}
 public System.IO.MemoryStream Info {
 get { return this._info; }
 set { this._info = value; }
}
 public bool IsSetInfo () {
 return this._info != null;
}
 public int ExpectedLength {
 get { return this._expectedLength.GetValueOrDefault(); }
 set { this._expectedLength = value; }
}
 public bool IsSetExpectedLength () {
 return this._expectedLength.HasValue;
}
 public void Validate() {
 if (!IsSetDigestAlgorithm()) throw new System.ArgumentException("Missing value for required property 'DigestAlgorithm'");
 if (!IsSetPrk()) throw new System.ArgumentException("Missing value for required property 'Prk'");
 if (!IsSetInfo()) throw new System.ArgumentException("Missing value for required property 'Info'");
 if (!IsSetExpectedLength()) throw new System.ArgumentException("Missing value for required property 'ExpectedLength'");

}
}
}
