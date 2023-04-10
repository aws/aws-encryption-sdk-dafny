// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class ValidEncryptionMaterialsTransitionInput {
 private AWS.Cryptography.MaterialProviders.EncryptionMaterials _start ;
 private AWS.Cryptography.MaterialProviders.EncryptionMaterials _stop ;
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials Start {
 get { return this._start; }
 set { this._start = value; }
}
 public bool IsSetStart () {
 return this._start != null;
}
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials Stop {
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
