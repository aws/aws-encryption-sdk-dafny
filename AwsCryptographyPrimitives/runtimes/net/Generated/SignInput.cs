// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class SignInput {
 private AWS.Cryptography.Primitives.ECDSASignatureAlgorithm _signatureAlgorithm ;
 private System.IO.MemoryStream _signingKey ;
 private System.IO.MemoryStream _message ;
 public AWS.Cryptography.Primitives.ECDSASignatureAlgorithm SignatureAlgorithm {
 get { return this._signatureAlgorithm; }
 set { this._signatureAlgorithm = value; }
}
 internal bool IsSetSignatureAlgorithm () {
 return this._signatureAlgorithm != null;
}
 public System.IO.MemoryStream SigningKey {
 get { return this._signingKey; }
 set { this._signingKey = value; }
}
 internal bool IsSetSigningKey () {
 return this._signingKey != null;
}
 public System.IO.MemoryStream Message {
 get { return this._message; }
 set { this._message = value; }
}
 internal bool IsSetMessage () {
 return this._message != null;
}
 public void Validate() {
 if (!IsSetSignatureAlgorithm()) throw new System.ArgumentException("Missing value for required property 'SignatureAlgorithm'");
 if (!IsSetSigningKey()) throw new System.ArgumentException("Missing value for required property 'SigningKey'");
 if (!IsSetMessage()) throw new System.ArgumentException("Missing value for required property 'Message'");

}
}
}
