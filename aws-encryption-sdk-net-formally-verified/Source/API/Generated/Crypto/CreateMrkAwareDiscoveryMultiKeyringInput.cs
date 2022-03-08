// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public class CreateMrkAwareDiscoveryMultiKeyringInput {
 private System.Collections.Generic.List<string> _regions ;
 private Aws.Crypto.DiscoveryFilter _discoveryFilter ;
 private Aws.Crypto.IClientSupplier _clientSupplier ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public System.Collections.Generic.List<string> Regions {
 get { return this._regions; }
 set { this._regions = value; }
}
 public Aws.Crypto.DiscoveryFilter DiscoveryFilter {
 get { return this._discoveryFilter; }
 set { this._discoveryFilter = value; }
}
 public Aws.Crypto.IClientSupplier ClientSupplier {
 get { return this._clientSupplier; }
 set { this._clientSupplier = value; }
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 public void Validate() {}
}
}
