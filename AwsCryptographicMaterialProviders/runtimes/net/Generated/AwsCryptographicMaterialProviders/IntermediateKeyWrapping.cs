// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class IntermediateKeyWrapping {
 private AWS.Cryptography.MaterialProviders.DerivationAlgorithm _keyEncryptionKeyKdf ;
 private AWS.Cryptography.MaterialProviders.DerivationAlgorithm _macKeyKdf ;
 private AWS.Cryptography.MaterialProviders.Encrypt _pdkEncryptAlgorithm ;
 public AWS.Cryptography.MaterialProviders.DerivationAlgorithm KeyEncryptionKeyKdf {
 get { return this._keyEncryptionKeyKdf; }
 set { this._keyEncryptionKeyKdf = value; }
}
 public bool IsSetKeyEncryptionKeyKdf () {
 return this._keyEncryptionKeyKdf != null;
}
 public AWS.Cryptography.MaterialProviders.DerivationAlgorithm MacKeyKdf {
 get { return this._macKeyKdf; }
 set { this._macKeyKdf = value; }
}
 public bool IsSetMacKeyKdf () {
 return this._macKeyKdf != null;
}
 public AWS.Cryptography.MaterialProviders.Encrypt PdkEncryptAlgorithm {
 get { return this._pdkEncryptAlgorithm; }
 set { this._pdkEncryptAlgorithm = value; }
}
 public bool IsSetPdkEncryptAlgorithm () {
 return this._pdkEncryptAlgorithm != null;
}
 public void Validate() {
 if (!IsSetKeyEncryptionKeyKdf()) throw new System.ArgumentException("Missing value for required property 'KeyEncryptionKeyKdf'");
 if (!IsSetMacKeyKdf()) throw new System.ArgumentException("Missing value for required property 'MacKeyKdf'");
 if (!IsSetPdkEncryptAlgorithm()) throw new System.ArgumentException("Missing value for required property 'PdkEncryptAlgorithm'");

}
}
}
