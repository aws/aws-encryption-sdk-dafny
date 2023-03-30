// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DecryptMaterialsInput {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _algorithmSuiteId ;
 private AWS.Cryptography.MaterialProviders.CommitmentPolicy _commitmentPolicy ;
 private System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> _encryptedDataKeys ;
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private System.Collections.Generic.Dictionary<string, string> _reproducedEncryptionContext ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 public bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public AWS.Cryptography.MaterialProviders.CommitmentPolicy CommitmentPolicy {
 get { return this._commitmentPolicy; }
 set { this._commitmentPolicy = value; }
}
 public bool IsSetCommitmentPolicy () {
 return this._commitmentPolicy != null;
}
 public System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> EncryptedDataKeys {
 get { return this._encryptedDataKeys; }
 set { this._encryptedDataKeys = value; }
}
 public bool IsSetEncryptedDataKeys () {
 return this._encryptedDataKeys != null;
}
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public System.Collections.Generic.Dictionary<string, string> ReproducedEncryptionContext {
 get { return this._reproducedEncryptionContext; }
 set { this._reproducedEncryptionContext = value; }
}
 public bool IsSetReproducedEncryptionContext () {
 return this._reproducedEncryptionContext != null;
}
 public void Validate() {
 if (!IsSetAlgorithmSuiteId()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuiteId'");
 if (!IsSetCommitmentPolicy()) throw new System.ArgumentException("Missing value for required property 'CommitmentPolicy'");
 if (!IsSetEncryptedDataKeys()) throw new System.ArgumentException("Missing value for required property 'EncryptedDataKeys'");
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");

}
}
}
