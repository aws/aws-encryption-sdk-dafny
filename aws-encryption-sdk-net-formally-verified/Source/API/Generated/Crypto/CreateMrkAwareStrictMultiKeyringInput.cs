// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public class CreateMrkAwareStrictMultiKeyringInput {
 private string _generator ;
 private System.Collections.Generic.List<string> _kmsKeyIds ;
 private Aws.Crypto.IClientSupplier _clientSupplier ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public string Generator {
 get { return this._generator; }
 set { this._generator = value; }
}
 public System.Collections.Generic.List<string> KmsKeyIds {
 get { return this._kmsKeyIds; }
 set { this._kmsKeyIds = value; }
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
