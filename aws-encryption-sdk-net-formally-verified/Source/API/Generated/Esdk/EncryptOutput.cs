// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Esdk
 ; namespace Aws.Esdk {
 public class EncryptOutput {
 private System.IO.MemoryStream _ciphertext ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId ;
 public System.IO.MemoryStream Ciphertext {
 get { return this._ciphertext; }
 set { this._ciphertext = value; }
}
 internal bool IsSetCiphertext () {
 return this._ciphertext != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 internal bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 internal bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public void Validate() {
 if (!IsSetCiphertext()) throw new System.ArgumentException("Missing value for required member 'ciphertext'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required member 'encryptionContext'");
 if (!IsSetAlgorithmSuiteId()) throw new System.ArgumentException("Missing value for required member 'algorithmSuiteId'");

}
}
}
