// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DecryptionMaterials {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo _algorithmSuite ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private System.Collections.Generic.List<string> _requiredEncryptionContextKeys ;
 private System.IO.MemoryStream _plaintextDataKey ;
 private System.IO.MemoryStream _verificationKey ;
 private System.IO.MemoryStream _symmetricSigningKey ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo AlgorithmSuite {
 get { return this._algorithmSuite; }
 set { this._algorithmSuite = value; }
}
 public bool IsSetAlgorithmSuite () {
 return this._algorithmSuite != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public System.Collections.Generic.List<string> RequiredEncryptionContextKeys {
 get { return this._requiredEncryptionContextKeys; }
 set { this._requiredEncryptionContextKeys = value; }
}
 public bool IsSetRequiredEncryptionContextKeys () {
 return this._requiredEncryptionContextKeys != null;
}
 public System.IO.MemoryStream PlaintextDataKey {
 get { return this._plaintextDataKey; }
 set { this._plaintextDataKey = value; }
}
 public bool IsSetPlaintextDataKey () {
 return this._plaintextDataKey != null;
}
 public System.IO.MemoryStream VerificationKey {
 get { return this._verificationKey; }
 set { this._verificationKey = value; }
}
 public bool IsSetVerificationKey () {
 return this._verificationKey != null;
}
 public System.IO.MemoryStream SymmetricSigningKey {
 get { return this._symmetricSigningKey; }
 set { this._symmetricSigningKey = value; }
}
 public bool IsSetSymmetricSigningKey () {
 return this._symmetricSigningKey != null;
}
 public void Validate() {
 if (!IsSetAlgorithmSuite()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuite'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
 if (!IsSetRequiredEncryptionContextKeys()) throw new System.ArgumentException("Missing value for required property 'RequiredEncryptionContextKeys'");

}
}
}
