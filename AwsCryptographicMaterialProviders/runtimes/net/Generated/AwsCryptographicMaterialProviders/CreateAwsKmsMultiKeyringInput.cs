// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateAwsKmsMultiKeyringInput {
 private string _generator ;
 private System.Collections.Generic.List<string> _kmsKeyIds ;
 private AWS.Cryptography.MaterialProviders.IClientSupplier _clientSupplier ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public string Generator {
 get { return this._generator; }
 set { this._generator = value; }
}
 public bool IsSetGenerator () {
 return this._generator != null;
}
 public System.Collections.Generic.List<string> KmsKeyIds {
 get { return this._kmsKeyIds; }
 set { this._kmsKeyIds = value; }
}
 public bool IsSetKmsKeyIds () {
 return this._kmsKeyIds != null;
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
 
}
}
}
