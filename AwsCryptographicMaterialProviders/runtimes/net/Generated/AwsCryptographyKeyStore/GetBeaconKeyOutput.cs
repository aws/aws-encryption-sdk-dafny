// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetBeaconKeyOutput {
 private AWS.Cryptography.MaterialProviders.BeaconKeyMaterials _beaconKeyMaterials ;
 public AWS.Cryptography.MaterialProviders.BeaconKeyMaterials BeaconKeyMaterials {
 get { return this._beaconKeyMaterials; }
 set { this._beaconKeyMaterials = value; }
}
 public bool IsSetBeaconKeyMaterials () {
 return this._beaconKeyMaterials != null;
}
 public void Validate() {
 if (!IsSetBeaconKeyMaterials()) throw new System.ArgumentException("Missing value for required property 'BeaconKeyMaterials'");

}
}
}
