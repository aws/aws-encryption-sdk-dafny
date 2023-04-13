// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetActiveBranchKeyInput {
 private string _branchKeyIdentifier ;
 private string _awsKmsKeyArn ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public string BranchKeyIdentifier {
 get { return this._branchKeyIdentifier; }
 set { this._branchKeyIdentifier = value; }
}
 public bool IsSetBranchKeyIdentifier () {
 return this._branchKeyIdentifier != null;
}
 public string AwsKmsKeyArn {
 get { return this._awsKmsKeyArn; }
 set { this._awsKmsKeyArn = value; }
}
 public bool IsSetAwsKmsKeyArn () {
 return this._awsKmsKeyArn != null;
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 public bool IsSetGrantTokens () {
 return this._grantTokens != null;
}
 public void Validate() {
 if (!IsSetBranchKeyIdentifier()) throw new System.ArgumentException("Missing value for required property 'BranchKeyIdentifier'");

}
}
}
