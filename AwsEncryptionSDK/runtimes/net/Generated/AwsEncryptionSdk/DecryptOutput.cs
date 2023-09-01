// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.EncryptionSDK; namespace AWS.Cryptography.EncryptionSDK {
 public class DecryptOutput {
 private System.IO.MemoryStream _plaintext ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private AWS.Cryptography.MaterialProviders.ESDKAlgorithmSuiteId _algorithmSuiteId ;
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
 public AWS.Cryptography.MaterialProviders.ESDKAlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 public bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public void Validate() {
 if (!IsSetPlaintext()) throw new System.ArgumentException("Missing value for required property 'Plaintext'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
 if (!IsSetAlgorithmSuiteId()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuiteId'");

}
}
}
