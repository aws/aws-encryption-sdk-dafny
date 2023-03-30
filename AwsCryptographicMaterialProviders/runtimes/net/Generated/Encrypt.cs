// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class Encrypt {
 private AWS.Cryptography.Primitives.AES_GCM _aES_GCM ;
 public AWS.Cryptography.Primitives.AES_GCM AES__GCM {
 get { return this._aES_GCM; }
 set { this._aES_GCM = value; }
}
 public bool IsSetAES__GCM () {
 return this._aES_GCM != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetAES__GCM()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
