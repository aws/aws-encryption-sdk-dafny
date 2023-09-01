// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.EncryptionSDK; namespace AWS.Cryptography.EncryptionSDK {
 public class EncryptInput {
 private System.IO.MemoryStream _plaintext ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager _materialsManager ;
 private AWS.Cryptography.MaterialProviders.IKeyring _keyring ;
 private AWS.Cryptography.MaterialProviders.ESDKAlgorithmSuiteId _algorithmSuiteId ;
 private long? _frameLength ;
 public System.IO.MemoryStream Plaintext {
 get { return this._plaintext; }
 set { this._plaintext = value; }
}
 public bool IsSetPlaintext () {
 return this._plaintext != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
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
 public AWS.Cryptography.MaterialProviders.ESDKAlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 public bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public long FrameLength {
 get { return this._frameLength.GetValueOrDefault(); }
 set { this._frameLength = value; }
}
 public bool IsSetFrameLength () {
 return this._frameLength.HasValue;
}
 public void Validate() {
 if (!IsSetPlaintext()) throw new System.ArgumentException("Missing value for required property 'Plaintext'");

}
}
}
