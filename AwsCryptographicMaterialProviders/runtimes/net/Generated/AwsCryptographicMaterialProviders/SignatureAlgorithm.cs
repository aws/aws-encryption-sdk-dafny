// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class SignatureAlgorithm {
 private AWS.Cryptography.MaterialProviders.ECDSA _eCDSA ;
 private AWS.Cryptography.MaterialProviders.None _none ;
 public AWS.Cryptography.MaterialProviders.ECDSA ECDSA {
 get { return this._eCDSA; }
 set { this._eCDSA = value; }
}
 public bool IsSetECDSA () {
 return this._eCDSA != null;
}
 public AWS.Cryptography.MaterialProviders.None None {
 get { return this._none; }
 set { this._none = value; }
}
 public bool IsSetNone () {
 return this._none != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetECDSA()) +
 Convert.ToUInt16(IsSetNone()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
