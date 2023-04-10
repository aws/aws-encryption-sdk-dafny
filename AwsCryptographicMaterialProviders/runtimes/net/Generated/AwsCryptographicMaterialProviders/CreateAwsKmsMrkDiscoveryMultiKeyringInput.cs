// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateAwsKmsMrkDiscoveryMultiKeyringInput {
 private System.Collections.Generic.List<string> _regions ;
 private AWS.Cryptography.MaterialProviders.DiscoveryFilter _discoveryFilter ;
 private AWS.Cryptography.MaterialProviders.IClientSupplier _clientSupplier ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public System.Collections.Generic.List<string> Regions {
 get { return this._regions; }
 set { this._regions = value; }
}
 public bool IsSetRegions () {
 return this._regions != null;
}
 public AWS.Cryptography.MaterialProviders.DiscoveryFilter DiscoveryFilter {
 get { return this._discoveryFilter; }
 set { this._discoveryFilter = value; }
}
 public bool IsSetDiscoveryFilter () {
 return this._discoveryFilter != null;
}
 public AWS.Cryptography.MaterialProviders.IClientSupplier ClientSupplier {
 get { return this._clientSupplier; }
 set { this._clientSupplier = value; }
}
 public bool IsSetClientSupplier () {
 return this._clientSupplier != null;
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 public bool IsSetGrantTokens () {
 return this._grantTokens != null;
}
 public void Validate() {
 if (!IsSetRegions()) throw new System.ArgumentException("Missing value for required property 'Regions'");

}
}
}
