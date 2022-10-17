// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class VerifyInput {
 private AWS.Cryptography.Primitives.ECDSASignatureAlgorithm _signatureAlgorithm ;
 private System.IO.MemoryStream _verificationKey ;
 private System.IO.MemoryStream _message ;
 private System.IO.MemoryStream _signature ;
 public AWS.Cryptography.Primitives.ECDSASignatureAlgorithm SignatureAlgorithm {
 get { return this._signatureAlgorithm; }
 set { this._signatureAlgorithm = value; }
}
 internal bool IsSetSignatureAlgorithm () {
 return this._signatureAlgorithm != null;
}
 public System.IO.MemoryStream VerificationKey {
 get { return this._verificationKey; }
 set { this._verificationKey = value; }
}
 internal bool IsSetVerificationKey () {
 return this._verificationKey != null;
}
 public System.IO.MemoryStream Message {
 get { return this._message; }
 set { this._message = value; }
}
 internal bool IsSetMessage () {
 return this._message != null;
}
 public System.IO.MemoryStream Signature {
 get { return this._signature; }
 set { this._signature = value; }
}
 internal bool IsSetSignature () {
 return this._signature != null;
}
 public void Validate() {
 if (!IsSetSignatureAlgorithm()) throw new System.ArgumentException("Missing value for required property 'SignatureAlgorithm'");
 if (!IsSetVerificationKey()) throw new System.ArgumentException("Missing value for required property 'VerificationKey'");
 if (!IsSetMessage()) throw new System.ArgumentException("Missing value for required property 'Message'");
 if (!IsSetSignature()) throw new System.ArgumentException("Missing value for required property 'Signature'");

}
}
}
