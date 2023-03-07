// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class ValidDecryptionMaterialsTransitionInput {
 private AWS.Cryptography.MaterialProviders.DecryptionMaterials _start ;
 private AWS.Cryptography.MaterialProviders.DecryptionMaterials _stop ;
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials Start {
 get { return this._start; }
 set { this._start = value; }
}
 public bool IsSetStart () {
 return this._start != null;
}
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials Stop {
 get { return this._stop; }
 set { this._stop = value; }
}
 public bool IsSetStop () {
 return this._stop != null;
}
 public void Validate() {
 if (!IsSetStart()) throw new System.ArgumentException("Missing value for required property 'Start'");
 if (!IsSetStop()) throw new System.ArgumentException("Missing value for required property 'Stop'");

}
}
}
