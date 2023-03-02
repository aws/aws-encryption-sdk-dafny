// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class Materials {
 private AWS.Cryptography.MaterialProviders.EncryptionMaterials _encryption ;
 private AWS.Cryptography.MaterialProviders.DecryptionMaterials _decryption ;
 private AWS.Cryptography.MaterialProviders.HierarchicalMaterials _hierarchical ;
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials Encryption {
 get { return this._encryption; }
 set { this._encryption = value; }
}
 internal bool IsSetEncryption () {
 return this._encryption != null;
}
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials Decryption {
 get { return this._decryption; }
 set { this._decryption = value; }
}
 internal bool IsSetDecryption () {
 return this._decryption != null;
}
 public AWS.Cryptography.MaterialProviders.HierarchicalMaterials Hierarchical {
 get { return this._hierarchical; }
 set { this._hierarchical = value; }
}
 internal bool IsSetHierarchical () {
 return this._hierarchical != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetEncryption()) +
 Convert.ToUInt16(IsSetDecryption()) +
 Convert.ToUInt16(IsSetHierarchical()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
