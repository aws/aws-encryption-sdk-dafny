// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GenerateECDSASignatureKeyOutput {
 private AWS.Cryptography.Primitives.ECDSASignatureAlgorithm _signatureAlgorithm ;
 private System.IO.MemoryStream _verificationKey ;
 private System.IO.MemoryStream _signingKey ;
 public AWS.Cryptography.Primitives.ECDSASignatureAlgorithm SignatureAlgorithm {
 get { return this._signatureAlgorithm; }
 set { this._signatureAlgorithm = value; }
}
 public bool IsSetSignatureAlgorithm () {
 return this._signatureAlgorithm != null;
}
 public System.IO.MemoryStream VerificationKey {
 get { return this._verificationKey; }
 set { this._verificationKey = value; }
}
 public bool IsSetVerificationKey () {
 return this._verificationKey != null;
}
 public System.IO.MemoryStream SigningKey {
 get { return this._signingKey; }
 set { this._signingKey = value; }
}
 public bool IsSetSigningKey () {
 return this._signingKey != null;
}
 public void Validate() {
 if (!IsSetSignatureAlgorithm()) throw new System.ArgumentException("Missing value for required property 'SignatureAlgorithm'");
 if (!IsSetVerificationKey()) throw new System.ArgumentException("Missing value for required property 'VerificationKey'");
 if (!IsSetSigningKey()) throw new System.ArgumentException("Missing value for required property 'SigningKey'");

}
}
}
