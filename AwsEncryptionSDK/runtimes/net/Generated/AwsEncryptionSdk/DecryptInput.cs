// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.EncryptionSDK; namespace AWS.Cryptography.EncryptionSDK {
 public class DecryptInput {
 private System.IO.MemoryStream _ciphertext ;
 private AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager _materialsManager ;
 private AWS.Cryptography.MaterialProviders.IKeyring _keyring ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 public System.IO.MemoryStream Ciphertext {
 get { return this._ciphertext; }
 set { this._ciphertext = value; }
}
 public bool IsSetCiphertext () {
 return this._ciphertext != null;
}
 public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager MaterialsManager {
 get { return this._materialsManager; }
 set { this._materialsManager = value; }
}
 public bool IsSetMaterialsManager () {
 return this._materialsManager != null;
}
 public AWS.Cryptography.MaterialProviders.IKeyring Keyring {
 get { return this._keyring; }
 set { this._keyring = value; }
}
 public bool IsSetKeyring () {
 return this._keyring != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public void Validate() {
 if (!IsSetCiphertext()) throw new System.ArgumentException("Missing value for required property 'Ciphertext'");

}
}
}
