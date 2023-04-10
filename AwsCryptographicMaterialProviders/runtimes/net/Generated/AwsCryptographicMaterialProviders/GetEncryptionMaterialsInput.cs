// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class GetEncryptionMaterialsInput {
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private AWS.Cryptography.MaterialProviders.CommitmentPolicy _commitmentPolicy ;
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _algorithmSuiteId ;
 private long? _maxPlaintextLength ;
 private System.Collections.Generic.List<string> _requiredEncryptionContextKeys ;
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public bool IsSetEncryptionContext () {
 return this._encryptionContext != null;
}
 public AWS.Cryptography.MaterialProviders.CommitmentPolicy CommitmentPolicy {
 get { return this._commitmentPolicy; }
 set { this._commitmentPolicy = value; }
}
 public bool IsSetCommitmentPolicy () {
 return this._commitmentPolicy != null;
}
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 public bool IsSetAlgorithmSuiteId () {
 return this._algorithmSuiteId != null;
}
 public long MaxPlaintextLength {
 get { return this._maxPlaintextLength.GetValueOrDefault(); }
 set { this._maxPlaintextLength = value; }
}
 public bool IsSetMaxPlaintextLength () {
 return this._maxPlaintextLength.HasValue;
}
 public System.Collections.Generic.List<string> RequiredEncryptionContextKeys {
 get { return this._requiredEncryptionContextKeys; }
 set { this._requiredEncryptionContextKeys = value; }
}
 public bool IsSetRequiredEncryptionContextKeys () {
 return this._requiredEncryptionContextKeys != null;
}
 public void Validate() {
 if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
 if (!IsSetCommitmentPolicy()) throw new System.ArgumentException("Missing value for required property 'CommitmentPolicy'");

}
}
}
