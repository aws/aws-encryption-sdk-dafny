// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class InitializeEncryptionMaterialsInput {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _algorithmSuiteId ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private System.IO.MemoryStream _signingKey ;
 private System.IO.MemoryStream _verificationKey ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 internal bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 internal bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public System.IO.MemoryStream SigningKey {
 get { return this._signingKey; }
 set { this._signingKey = value; }
}
 internal bool IsSetSigningKey () {
 return this._signingKey != null;
}
 public System.IO.MemoryStream VerificationKey {
 get { return this._verificationKey; }
 set { this._verificationKey = value; }
}
 internal bool IsSetVerificationKey () {
 return this._verificationKey != null;
}
 public void Validate() {
 if (!IsSetAlgorithmSuiteId()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuiteId'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");

}
}
}
