// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DerivationAlgorithm {
 private AWS.Cryptography.MaterialProviders.HKDF _hKDF ;
 private AWS.Cryptography.MaterialProviders.IDENTITY _iDENTITY ;
 private AWS.Cryptography.MaterialProviders.None _none ;
 public AWS.Cryptography.MaterialProviders.HKDF HKDF {
 get { return this._hKDF; }
 set { this._hKDF = value; }
}
 public bool IsSetHKDF () {
 return this._hKDF != null;
}
 public AWS.Cryptography.MaterialProviders.IDENTITY IDENTITY {
 get { return this._iDENTITY; }
 set { this._iDENTITY = value; }
}
 public bool IsSetIDENTITY () {
 return this._iDENTITY != null;
}
 public AWS.Cryptography.MaterialProviders.None None {
 get { return this._none; }
 set { this._none = value; }
}
 public bool IsSetNone () {
 return this._none != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetHKDF()) +
 Convert.ToUInt16(IsSetIDENTITY()) +
 Convert.ToUInt16(IsSetNone()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
