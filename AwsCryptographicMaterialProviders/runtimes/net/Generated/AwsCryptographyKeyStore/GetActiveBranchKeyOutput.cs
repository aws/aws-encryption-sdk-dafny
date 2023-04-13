// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetActiveBranchKeyOutput {
 private AWS.Cryptography.MaterialProviders.HierarchicalMaterials _hierarchicalMaterials ;
 public AWS.Cryptography.MaterialProviders.HierarchicalMaterials HierarchicalMaterials {
 get { return this._hierarchicalMaterials; }
 set { this._hierarchicalMaterials = value; }
}
 public bool IsSetHierarchicalMaterials () {
 return this._hierarchicalMaterials != null;
}
 public void Validate() {
 if (!IsSetHierarchicalMaterials()) throw new System.ArgumentException("Missing value for required property 'HierarchicalMaterials'");

}
}
}
