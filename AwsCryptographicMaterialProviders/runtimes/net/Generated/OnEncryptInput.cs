// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class OnEncryptInput {
 private AWS.Cryptography.MaterialProviders.EncryptionMaterials _materials ;
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials Materials {
 get { return this._materials; }
 set { this._materials = value; }
}
 public bool IsSetMaterials () {
 return this._materials != null;
}
 public void Validate() {
 if (!IsSetMaterials()) throw new System.ArgumentException("Missing value for required property 'Materials'");

}
}
}
