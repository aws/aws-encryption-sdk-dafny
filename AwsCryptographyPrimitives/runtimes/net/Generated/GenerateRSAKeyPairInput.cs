// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GenerateRSAKeyPairInput {
 private int? _strength ;
 public int Strength {
 get { return this._strength.GetValueOrDefault(); }
 set { this._strength = value; }
}
 public bool IsSetStrength () {
 return this._strength.HasValue;
}
 public void Validate() {
 if (!IsSetStrength()) throw new System.ArgumentException("Missing value for required property 'Strength'");

}
}
}
