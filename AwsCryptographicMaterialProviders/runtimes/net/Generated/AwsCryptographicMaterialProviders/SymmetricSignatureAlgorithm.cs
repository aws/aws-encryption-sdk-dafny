// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class SymmetricSignatureAlgorithm {
 private AWS.Cryptography.Primitives.DigestAlgorithm _hMAC ;
 private AWS.Cryptography.MaterialProviders.None _none ;
 public AWS.Cryptography.Primitives.DigestAlgorithm HMAC {
 get { return this._hMAC; }
 set { this._hMAC = value; }
}
 public bool IsSetHMAC () {
 return this._hMAC != null;
}
 public AWS.Cryptography.MaterialProviders.None None {
 get { return this._none; }
 set { this._none = value; }
}
 public bool IsSetNone () {
 return this._none != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetHMAC()) +
 Convert.ToUInt16(IsSetNone()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
