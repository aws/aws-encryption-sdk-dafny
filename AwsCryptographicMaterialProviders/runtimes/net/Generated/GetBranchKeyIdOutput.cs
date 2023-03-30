// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class GetBranchKeyIdOutput {
 private string _branchKeyId ;
 public string BranchKeyId {
 get { return this._branchKeyId; }
 set { this._branchKeyId = value; }
}
 public bool IsSetBranchKeyId () {
 return this._branchKeyId != null;
}
 public void Validate() {
 if (!IsSetBranchKeyId()) throw new System.ArgumentException("Missing value for required property 'BranchKeyId'");

}
}
}
