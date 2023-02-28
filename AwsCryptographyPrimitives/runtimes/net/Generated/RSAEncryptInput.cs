// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class RSAEncryptInput {
 private AWS.Cryptography.Primitives.RSAPaddingMode _padding ;
 private System.IO.MemoryStream _publicKey ;
 private System.IO.MemoryStream _plaintext ;
 public AWS.Cryptography.Primitives.RSAPaddingMode Padding {
 get { return this._padding; }
 set { this._padding = value; }
}
 public bool IsSetPadding () {
 return this._padding != null;
}
 public System.IO.MemoryStream PublicKey {
 get { return this._publicKey; }
 set { this._publicKey = value; }
}
 public bool IsSetPublicKey () {
 return this._publicKey != null;
}
 public System.IO.MemoryStream Plaintext {
 get { return this._plaintext; }
 set { this._plaintext = value; }
}
 public bool IsSetPlaintext () {
 return this._plaintext != null;
}
 public void Validate() {
 if (!IsSetPadding()) throw new System.ArgumentException("Missing value for required property 'Padding'");
 if (!IsSetPublicKey()) throw new System.ArgumentException("Missing value for required property 'PublicKey'");
 if (!IsSetPlaintext()) throw new System.ArgumentException("Missing value for required property 'Plaintext'");

}
}
}
