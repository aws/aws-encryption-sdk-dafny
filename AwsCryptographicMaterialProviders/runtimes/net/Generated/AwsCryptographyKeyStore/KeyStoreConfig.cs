// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class KeyStoreConfig {
 private string _ddbTableName ;
 private AWS.Cryptography.KeyStore.KMSConfiguration _kmsConfiguration ;
 private string _logicalKeyStoreName ;
 private string _id ;
 private System.Collections.Generic.List<string> _grantTokens ;
 private Amazon.DynamoDBv2.IAmazonDynamoDB _ddbClient ;
 private Amazon.KeyManagementService.IAmazonKeyManagementService _kmsClient ;
 public string DdbTableName {
 get { return this._ddbTableName; }
 set { this._ddbTableName = value; }
}
 public bool IsSetDdbTableName () {
 return this._ddbTableName != null;
}
 public AWS.Cryptography.KeyStore.KMSConfiguration KmsConfiguration {
 get { return this._kmsConfiguration; }
 set { this._kmsConfiguration = value; }
}
 public bool IsSetKmsConfiguration () {
 return this._kmsConfiguration != null;
}
 public string LogicalKeyStoreName {
 get { return this._logicalKeyStoreName; }
 set { this._logicalKeyStoreName = value; }
}
 public bool IsSetLogicalKeyStoreName () {
 return this._logicalKeyStoreName != null;
}
 public string Id {
 get { return this._id; }
 set { this._id = value; }
}
 public bool IsSetId () {
 return this._id != null;
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 public bool IsSetGrantTokens () {
 return this._grantTokens != null;
}
 public Amazon.DynamoDBv2.IAmazonDynamoDB DdbClient {
 get { return this._ddbClient; }
 set { this._ddbClient = value; }
}
 public bool IsSetDdbClient () {
 return this._ddbClient != null;
}
 public Amazon.KeyManagementService.IAmazonKeyManagementService KmsClient {
 get { return this._kmsClient; }
 set { this._kmsClient = value; }
}
 public bool IsSetKmsClient () {
 return this._kmsClient != null;
}
 public void Validate() {
 if (!IsSetDdbTableName()) throw new System.ArgumentException("Missing value for required property 'DdbTableName'");
 if (!IsSetKmsConfiguration()) throw new System.ArgumentException("Missing value for required property 'KmsConfiguration'");
 if (!IsSetLogicalKeyStoreName()) throw new System.ArgumentException("Missing value for required property 'LogicalKeyStoreName'");

}
}
}
