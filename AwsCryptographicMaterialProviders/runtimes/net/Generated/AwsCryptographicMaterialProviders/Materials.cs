// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class Materials {
 private AWS.Cryptography.MaterialProviders.EncryptionMaterials _encryption ;
 private AWS.Cryptography.MaterialProviders.DecryptionMaterials _decryption ;
 private AWS.Cryptography.MaterialProviders.BranchKeyMaterials _branchKey ;
 private AWS.Cryptography.MaterialProviders.BeaconKeyMaterials _beaconKey ;
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials Encryption {
 get { return this._encryption; }
 set { this._encryption = value; }
}
 public bool IsSetEncryption () {
 return this._encryption != null;
}
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials Decryption {
 get { return this._decryption; }
 set { this._decryption = value; }
}
 public bool IsSetDecryption () {
 return this._decryption != null;
}
 public AWS.Cryptography.MaterialProviders.BranchKeyMaterials BranchKey {
 get { return this._branchKey; }
 set { this._branchKey = value; }
}
 public bool IsSetBranchKey () {
 return this._branchKey != null;
}
 public AWS.Cryptography.MaterialProviders.BeaconKeyMaterials BeaconKey {
 get { return this._beaconKey; }
 set { this._beaconKey = value; }
}
 public bool IsSetBeaconKey () {
 return this._beaconKey != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetEncryption()) +
 Convert.ToUInt16(IsSetDecryption()) +
 Convert.ToUInt16(IsSetBranchKey()) +
 Convert.ToUInt16(IsSetBeaconKey()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
