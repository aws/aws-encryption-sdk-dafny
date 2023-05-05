// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class GetKeyStoreInfoOutput {
 private string _keyStoreId ;
 private string _keyStoreName ;
 private string _logicalKeyStoreName ;
 private System.Collections.Generic.List<string> _grantTokens ;
 private AWS.Cryptography.KeyStore.KMSConfiguration _kmsConfiguration ;
 public string KeyStoreId {
 get { return this._keyStoreId; }
 set { this._keyStoreId = value; }
}
 public bool IsSetKeyStoreId () {
 return this._keyStoreId != null;
}
 public string KeyStoreName {
 get { return this._keyStoreName; }
 set { this._keyStoreName = value; }
}
 public bool IsSetKeyStoreName () {
 return this._keyStoreName != null;
}
 public string LogicalKeyStoreName {
 get { return this._logicalKeyStoreName; }
 set { this._logicalKeyStoreName = value; }
}
 public bool IsSetLogicalKeyStoreName () {
 return this._logicalKeyStoreName != null;
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 public bool IsSetGrantTokens () {
 return this._grantTokens != null;
}
 public AWS.Cryptography.KeyStore.KMSConfiguration KmsConfiguration {
 get { return this._kmsConfiguration; }
 set { this._kmsConfiguration = value; }
}
 public bool IsSetKmsConfiguration () {
 return this._kmsConfiguration != null;
}
 public void Validate() {
 if (!IsSetKeyStoreId()) throw new System.ArgumentException("Missing value for required property 'KeyStoreId'");
 if (!IsSetKeyStoreName()) throw new System.ArgumentException("Missing value for required property 'KeyStoreName'");
 if (!IsSetLogicalKeyStoreName()) throw new System.ArgumentException("Missing value for required property 'LogicalKeyStoreName'");
 if (!IsSetGrantTokens()) throw new System.ArgumentException("Missing value for required property 'GrantTokens'");
 if (!IsSetKmsConfiguration()) throw new System.ArgumentException("Missing value for required property 'KmsConfiguration'");

}
}
}
