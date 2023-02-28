// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class RSADecryptInput {
 private AWS.Cryptography.Primitives.RSAPaddingMode _padding ;
 private System.IO.MemoryStream _privateKey ;
 private System.IO.MemoryStream _cipherText ;
 public AWS.Cryptography.Primitives.RSAPaddingMode Padding {
 get { return this._padding; }
 set { this._padding = value; }
}
 public bool IsSetPadding () {
 return this._padding != null;
}
 public System.IO.MemoryStream PrivateKey {
 get { return this._privateKey; }
 set { this._privateKey = value; }
}
 public bool IsSetPrivateKey () {
 return this._privateKey != null;
}
 public System.IO.MemoryStream CipherText {
 get { return this._cipherText; }
 set { this._cipherText = value; }
}
 public bool IsSetCipherText () {
 return this._cipherText != null;
}
 public void Validate() {
 if (!IsSetPadding()) throw new System.ArgumentException("Missing value for required property 'Padding'");
 if (!IsSetPrivateKey()) throw new System.ArgumentException("Missing value for required property 'PrivateKey'");
 if (!IsSetCipherText()) throw new System.ArgumentException("Missing value for required property 'CipherText'");

}
}
}
