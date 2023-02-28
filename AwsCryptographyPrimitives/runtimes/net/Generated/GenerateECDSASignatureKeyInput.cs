// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GenerateECDSASignatureKeyInput {
 private AWS.Cryptography.Primitives.ECDSASignatureAlgorithm _signatureAlgorithm ;
 public AWS.Cryptography.Primitives.ECDSASignatureAlgorithm SignatureAlgorithm {
 get { return this._signatureAlgorithm; }
 set { this._signatureAlgorithm = value; }
}
 public bool IsSetSignatureAlgorithm () {
 return this._signatureAlgorithm != null;
}
 public void Validate() {
 if (!IsSetSignatureAlgorithm()) throw new System.ArgumentException("Missing value for required property 'SignatureAlgorithm'");

}
}
}
