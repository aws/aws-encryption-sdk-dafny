// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetActiveBranchKeyOutput {
 private AWS.Cryptography.MaterialProviders.BranchKeyMaterials _branchKeyMaterials ;
 public AWS.Cryptography.MaterialProviders.BranchKeyMaterials BranchKeyMaterials {
 get { return this._branchKeyMaterials; }
 set { this._branchKeyMaterials = value; }
}
 public bool IsSetBranchKeyMaterials () {
 return this._branchKeyMaterials != null;
}
 public void Validate() {
 if (!IsSetBranchKeyMaterials()) throw new System.ArgumentException("Missing value for required property 'BranchKeyMaterials'");

}
}
}
