// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetBeaconKeyOutput {
 private System.IO.MemoryStream _beaconKey ;
 public System.IO.MemoryStream BeaconKey {
 get { return this._beaconKey; }
 set { this._beaconKey = value; }
}
 public bool IsSetBeaconKey () {
 return this._beaconKey != null;
}
 public void Validate() {
 if (!IsSetBeaconKey()) throw new System.ArgumentException("Missing value for required property 'BeaconKey'");

}
}
}
