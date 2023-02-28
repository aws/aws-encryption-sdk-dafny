// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class GenerateRandomBytesInput {
 private int? _length ;
 public int Length {
 get { return this._length.GetValueOrDefault(); }
 set { this._length = value; }
}
 public bool IsSetLength () {
 return this._length.HasValue;
}
 public void Validate() {
 if (!IsSetLength()) throw new System.ArgumentException("Missing value for required property 'Length'");

}
}
}
