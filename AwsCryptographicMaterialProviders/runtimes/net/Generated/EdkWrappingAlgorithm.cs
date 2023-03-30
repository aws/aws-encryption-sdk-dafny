// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class EdkWrappingAlgorithm {
 private AWS.Cryptography.MaterialProviders.DIRECT_KEY_WRAPPING _dIRECT_KEY_WRAPPING ;
 private AWS.Cryptography.MaterialProviders.IntermediateKeyWrapping _intermediateKeyWrapping ;
 public AWS.Cryptography.MaterialProviders.DIRECT_KEY_WRAPPING DIRECT__KEY__WRAPPING {
 get { return this._dIRECT_KEY_WRAPPING; }
 set { this._dIRECT_KEY_WRAPPING = value; }
}
 public bool IsSetDIRECT__KEY__WRAPPING () {
 return this._dIRECT_KEY_WRAPPING != null;
}
 public AWS.Cryptography.MaterialProviders.IntermediateKeyWrapping IntermediateKeyWrapping {
 get { return this._intermediateKeyWrapping; }
 set { this._intermediateKeyWrapping = value; }
}
 public bool IsSetIntermediateKeyWrapping () {
 return this._intermediateKeyWrapping != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetDIRECT__KEY__WRAPPING()) +
 Convert.ToUInt16(IsSetIntermediateKeyWrapping()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
