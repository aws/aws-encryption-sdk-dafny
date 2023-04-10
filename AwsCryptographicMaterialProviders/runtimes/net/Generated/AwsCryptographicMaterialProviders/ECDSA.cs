// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class ECDSA {
 private AWS.Cryptography.Primitives.ECDSASignatureAlgorithm _curve ;
 public AWS.Cryptography.Primitives.ECDSASignatureAlgorithm Curve {
 get { return this._curve; }
 set { this._curve = value; }
}
 public bool IsSetCurve () {
 return this._curve != null;
}
 public void Validate() {
 if (!IsSetCurve()) throw new System.ArgumentException("Missing value for required property 'Curve'");

}
}
}
