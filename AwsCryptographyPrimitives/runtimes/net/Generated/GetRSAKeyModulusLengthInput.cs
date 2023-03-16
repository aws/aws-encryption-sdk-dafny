// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GetRSAKeyModulusLengthInput {
 private System.IO.MemoryStream _publicKey ;
 public System.IO.MemoryStream PublicKey {
 get { return this._publicKey; }
 set { this._publicKey = value; }
}
 public bool IsSetPublicKey () {
 return this._publicKey != null;
}
 public void Validate() {
 if (!IsSetPublicKey()) throw new System.ArgumentException("Missing value for required property 'PublicKey'");

}
}
}
