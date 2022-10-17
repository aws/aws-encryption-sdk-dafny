// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class HkdfExtractInput {
 private AWS.Cryptography.Primitives.DigestAlgorithm _digestAlgorithm ;
 private System.IO.MemoryStream _salt ;
 private System.IO.MemoryStream _ikm ;
 public AWS.Cryptography.Primitives.DigestAlgorithm DigestAlgorithm {
 get { return this._digestAlgorithm; }
 set { this._digestAlgorithm = value; }
}
 internal bool IsSetDigestAlgorithm () {
 return this._digestAlgorithm != null;
}
 public System.IO.MemoryStream Salt {
 get { return this._salt; }
 set { this._salt = value; }
}
 internal bool IsSetSalt () {
 return this._salt != null;
}
 public System.IO.MemoryStream Ikm {
 get { return this._ikm; }
 set { this._ikm = value; }
}
 internal bool IsSetIkm () {
 return this._ikm != null;
}
 public void Validate() {
 if (!IsSetDigestAlgorithm()) throw new System.ArgumentException("Missing value for required property 'DigestAlgorithm'");
 if (!IsSetIkm()) throw new System.ArgumentException("Missing value for required property 'Ikm'");

}
}
}
