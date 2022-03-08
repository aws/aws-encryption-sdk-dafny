// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public class PutEntryForDecryptInput {
 private System.IO.MemoryStream _identifier ;
 private Aws.Crypto.DecryptionMaterials _decryptionMaterials ;
 public System.IO.MemoryStream Identifier {
 get { return this._identifier; }
 set { this._identifier = value; }
}
 public Aws.Crypto.DecryptionMaterials DecryptionMaterials {
 get { return this._decryptionMaterials; }
 set { this._decryptionMaterials = value; }
}
 public void Validate() {}
}
}
