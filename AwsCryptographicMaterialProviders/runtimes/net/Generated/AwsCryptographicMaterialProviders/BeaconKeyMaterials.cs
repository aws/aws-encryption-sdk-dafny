// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class BeaconKeyMaterials {
 private string _beaconKeyIdentifier ;
 private System.IO.MemoryStream _beaconKey ;
 private System.Collections.Generic.List<System.IO.MemoryStream> _hmacKeys ;
 public string BeaconKeyIdentifier {
 get { return this._beaconKeyIdentifier; }
 set { this._beaconKeyIdentifier = value; }
}
 public bool IsSetBeaconKeyIdentifier () {
 return this._beaconKeyIdentifier != null;
}
 public System.IO.MemoryStream BeaconKey {
 get { return this._beaconKey; }
 set { this._beaconKey = value; }
}
 public bool IsSetBeaconKey () {
 return this._beaconKey != null;
}
 public System.Collections.Generic.List<System.IO.MemoryStream> HmacKeys {
 get { return this._hmacKeys; }
 set { this._hmacKeys = value; }
}
 public bool IsSetHmacKeys () {
 return this._hmacKeys != null;
}
 public void Validate() {
 if (!IsSetBeaconKeyIdentifier()) throw new System.ArgumentException("Missing value for required property 'BeaconKeyIdentifier'");

}
}
}
