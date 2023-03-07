// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class ValidateCommitmentPolicyOnDecryptInput {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _algorithm ;
 private AWS.Cryptography.MaterialProviders.CommitmentPolicy _commitmentPolicy ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId Algorithm {
 get { return this._algorithm; }
 set { this._algorithm = value; }
}
 public bool IsSetAlgorithm () {
 return this._algorithm != null;
}
 public AWS.Cryptography.MaterialProviders.CommitmentPolicy CommitmentPolicy {
 get { return this._commitmentPolicy; }
 set { this._commitmentPolicy = value; }
}
 public bool IsSetCommitmentPolicy () {
 return this._commitmentPolicy != null;
}
 public void Validate() {
 if (!IsSetAlgorithm()) throw new System.ArgumentException("Missing value for required property 'Algorithm'");
 if (!IsSetCommitmentPolicy()) throw new System.ArgumentException("Missing value for required property 'CommitmentPolicy'");

}
}
}
