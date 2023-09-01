// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.EncryptionSDK; namespace AWS.Cryptography.EncryptionSDK {
 public class AwsEncryptionSdkConfig {
 private AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy _commitmentPolicy ;
 private long? _maxEncryptedDataKeys ;
 public AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy CommitmentPolicy {
 get { return this._commitmentPolicy; }
 set { this._commitmentPolicy = value; }
}
 public bool IsSetCommitmentPolicy () {
 return this._commitmentPolicy != null;
}
 public long MaxEncryptedDataKeys {
 get { return this._maxEncryptedDataKeys.GetValueOrDefault(); }
 set { this._maxEncryptedDataKeys = value; }
}
 public bool IsSetMaxEncryptedDataKeys () {
 return this._maxEncryptedDataKeys.HasValue;
}
 public void Validate() {
 
}
}
}
