// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CommitmentPolicy {
 private AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy _eSDK ;
 public AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy ESDK {
 get { return this._eSDK; }
 set { this._eSDK = value; }
}
 internal bool IsSetESDK () {
 return this._eSDK != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetESDK()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
