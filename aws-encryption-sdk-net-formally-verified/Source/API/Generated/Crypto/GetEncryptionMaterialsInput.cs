// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public class GetEncryptionMaterialsInput {
 private System.Collections.Generic.Dictionary<string, string> _encryptionContext ;
 private Aws.Crypto.CommitmentPolicy _commitmentPolicy ;
 private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId ;
 private long? _maxPlaintextLength ;
 public System.Collections.Generic.Dictionary<string, string> EncryptionContext {
 get { return this._encryptionContext; }
 set { this._encryptionContext = value; }
}
 public Aws.Crypto.CommitmentPolicy CommitmentPolicy {
 get { return this._commitmentPolicy; }
 set { this._commitmentPolicy = value; }
}
 public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId {
 get { return this._algorithmSuiteId; }
 set { this._algorithmSuiteId = value; }
}
 public long MaxPlaintextLength {
 get { return this._maxPlaintextLength.GetValueOrDefault(); }
 set { this._maxPlaintextLength = value; }
}
 public void Validate() {}
}
}
