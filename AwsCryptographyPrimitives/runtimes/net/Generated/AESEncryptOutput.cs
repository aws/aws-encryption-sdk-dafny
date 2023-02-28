// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class AESEncryptOutput {
 private System.IO.MemoryStream _cipherText ;
 private System.IO.MemoryStream _authTag ;
 public System.IO.MemoryStream CipherText {
 get { return this._cipherText; }
 set { this._cipherText = value; }
}
 public bool IsSetCipherText () {
 return this._cipherText != null;
}
 public System.IO.MemoryStream AuthTag {
 get { return this._authTag; }
 set { this._authTag = value; }
}
 public bool IsSetAuthTag () {
 return this._authTag != null;
}
 public void Validate() {
 if (!IsSetCipherText()) throw new System.ArgumentException("Missing value for required property 'CipherText'");
 if (!IsSetAuthTag()) throw new System.ArgumentException("Missing value for required property 'AuthTag'");

}
}
}
