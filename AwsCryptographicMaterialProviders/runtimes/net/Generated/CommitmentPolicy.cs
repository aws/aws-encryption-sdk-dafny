// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CommitmentPolicy {
 private AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy _eSDK ;
 private AWS.Cryptography.MaterialProviders.DBECommitmentPolicy _dBE ;
 public AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy ESDK {
 get { return this._eSDK; }
 set { this._eSDK = value; }
}
 public bool IsSetESDK () {
 return this._eSDK != null;
}
 public AWS.Cryptography.MaterialProviders.DBECommitmentPolicy DBE {
 get { return this._dBE; }
 set { this._dBE = value; }
}
 public bool IsSetDBE () {
 return this._dBE != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetESDK()) +
 Convert.ToUInt16(IsSetDBE()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
