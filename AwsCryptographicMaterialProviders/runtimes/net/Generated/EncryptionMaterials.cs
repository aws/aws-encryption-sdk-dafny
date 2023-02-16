// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class EncryptionMaterials {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo _algorithmSuite ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> _encryptedDataKeys ;
 private System.IO.MemoryStream _plaintextDataKey ;
 private System.IO.MemoryStream _signingKey ;
 private System.Collections.Generic.List<System.IO.MemoryStream> _symmetricSigningKeys ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo AlgorithmSuite {
 get { return this._algorithmSuite; }
 set { this._algorithmSuite = value; }
}
 internal bool IsSetAlgorithmSuite () {
 return this._algorithmSuite != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 internal bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> EncryptedDataKeys {
 get { return this._encryptedDataKeys; }
 set { this._encryptedDataKeys = value; }
}
 internal bool IsSetEncryptedDataKeys () {
 return this._encryptedDataKeys != null;
}
 public System.IO.MemoryStream PlaintextDataKey {
 get { return this._plaintextDataKey; }
 set { this._plaintextDataKey = value; }
}
 internal bool IsSetPlaintextDataKey () {
 return this._plaintextDataKey != null;
}
 public System.IO.MemoryStream SigningKey {
 get { return this._signingKey; }
 set { this._signingKey = value; }
}
 internal bool IsSetSigningKey () {
 return this._signingKey != null;
}
 public System.Collections.Generic.List<System.IO.MemoryStream> SymmetricSigningKeys {
 get { return this._symmetricSigningKeys; }
 set { this._symmetricSigningKeys = value; }
}
 internal bool IsSetSymmetricSigningKeys () {
 return this._symmetricSigningKeys != null;
}
 public void Validate() {
 if (!IsSetAlgorithmSuite()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuite'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
 if (!IsSetEncryptedDataKeys()) throw new System.ArgumentException("Missing value for required property 'EncryptedDataKeys'");

}
}
}
