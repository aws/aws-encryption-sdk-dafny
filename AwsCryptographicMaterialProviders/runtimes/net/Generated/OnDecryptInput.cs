// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class OnDecryptInput {
 private AWS.Cryptography.MaterialProviders.DecryptionMaterials _materials ;
 private System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> _encryptedDataKeys ;
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials Materials {
 get { return this._materials; }
 set { this._materials = value; }
}
 public bool IsSetMaterials () {
 return this._materials != null;
}
 public System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.EncryptedDataKey> EncryptedDataKeys {
 get { return this._encryptedDataKeys; }
 set { this._encryptedDataKeys = value; }
}
 public bool IsSetEncryptedDataKeys () {
 return this._encryptedDataKeys != null;
}
 public void Validate() {
 if (!IsSetMaterials()) throw new System.ArgumentException("Missing value for required property 'Materials'");
 if (!IsSetEncryptedDataKeys()) throw new System.ArgumentException("Missing value for required property 'EncryptedDataKeys'");

}
}
}
