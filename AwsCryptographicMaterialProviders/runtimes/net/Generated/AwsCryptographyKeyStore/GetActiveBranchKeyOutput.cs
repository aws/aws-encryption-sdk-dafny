// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetActiveBranchKeyOutput {
 private System.IO.MemoryStream _branchKey ;
 private string _branchKeyVersion ;
 private string _awsKmsKeyArn ;
 public System.IO.MemoryStream BranchKey {
 get { return this._branchKey; }
 set { this._branchKey = value; }
}
 public bool IsSetBranchKey () {
 return this._branchKey != null;
}
 public string BranchKeyVersion {
 get { return this._branchKeyVersion; }
 set { this._branchKeyVersion = value; }
}
 public bool IsSetBranchKeyVersion () {
 return this._branchKeyVersion != null;
}
 public string AwsKmsKeyArn {
 get { return this._awsKmsKeyArn; }
 set { this._awsKmsKeyArn = value; }
}
 public bool IsSetAwsKmsKeyArn () {
 return this._awsKmsKeyArn != null;
}
 public void Validate() {
 if (!IsSetBranchKey()) throw new System.ArgumentException("Missing value for required property 'BranchKey'");
 if (!IsSetBranchKeyVersion()) throw new System.ArgumentException("Missing value for required property 'BranchKeyVersion'");

}
}
}
