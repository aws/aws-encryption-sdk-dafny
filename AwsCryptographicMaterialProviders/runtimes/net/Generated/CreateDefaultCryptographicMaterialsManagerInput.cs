// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateDefaultCryptographicMaterialsManagerInput {
 private AWS.Cryptography.MaterialProviders.IKeyring _keyring ;
 public AWS.Cryptography.MaterialProviders.IKeyring Keyring {
 get { return this._keyring; }
 set { this._keyring = value; }
}
 public bool IsSetKeyring () {
 return this._keyring != null;
}
 public void Validate() {
 if (!IsSetKeyring()) throw new System.ArgumentException("Missing value for required property 'Keyring'");

}
}
}
