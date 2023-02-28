// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class DigestInput {
 private AWS.Cryptography.Primitives.DigestAlgorithm _digestAlgorithm ;
 private System.IO.MemoryStream _message ;
 public AWS.Cryptography.Primitives.DigestAlgorithm DigestAlgorithm {
 get { return this._digestAlgorithm; }
 set { this._digestAlgorithm = value; }
}
 public bool IsSetDigestAlgorithm () {
 return this._digestAlgorithm != null;
}
 public System.IO.MemoryStream Message {
 get { return this._message; }
 set { this._message = value; }
}
 public bool IsSetMessage () {
 return this._message != null;
}
 public void Validate() {
 if (!IsSetDigestAlgorithm()) throw new System.ArgumentException("Missing value for required property 'DigestAlgorithm'");
 if (!IsSetMessage()) throw new System.ArgumentException("Missing value for required property 'Message'");

}
}
}
