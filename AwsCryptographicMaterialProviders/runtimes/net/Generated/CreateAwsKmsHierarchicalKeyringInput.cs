// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateAwsKmsHierarchicalKeyringInput {
 private string _branchKeyId ;
 private string _kmsKeyId ;
 private Amazon.KeyManagementService.IAmazonKeyManagementService _kmsClient ;
 private Amazon.DynamoDBv2.IAmazonDynamoDB _ddbClient ;
 private string _branchKeysTableName ;
 private long? _ttlMilliseconds ;
 private int? _maxCacheSize ;
 private System.Collections.Generic.List<string> _grantTokens ;
 public string BranchKeyId {
 get { return this._branchKeyId; }
 set { this._branchKeyId = value; }
}
 internal bool IsSetBranchKeyId () {
 return this._branchKeyId != null;
}
 public string KmsKeyId {
 get { return this._kmsKeyId; }
 set { this._kmsKeyId = value; }
}
 internal bool IsSetKmsKeyId () {
 return this._kmsKeyId != null;
}
 public Amazon.KeyManagementService.IAmazonKeyManagementService KmsClient {
 get { return this._kmsClient; }
 set { this._kmsClient = value; }
}
 internal bool IsSetKmsClient () {
 return this._kmsClient != null;
}
 public Amazon.DynamoDBv2.IAmazonDynamoDB DdbClient {
 get { return this._ddbClient; }
 set { this._ddbClient = value; }
}
 internal bool IsSetDdbClient () {
 return this._ddbClient != null;
}
 public string BranchKeysTableName {
 get { return this._branchKeysTableName; }
 set { this._branchKeysTableName = value; }
}
 internal bool IsSetBranchKeysTableName () {
 return this._branchKeysTableName != null;
}
 public long TtlMilliseconds {
 get { return this._ttlMilliseconds.GetValueOrDefault(); }
 set { this._ttlMilliseconds = value; }
}
 internal bool IsSetTtlMilliseconds () {
 return this._ttlMilliseconds.HasValue;
}
 public int MaxCacheSize {
 get { return this._maxCacheSize.GetValueOrDefault(); }
 set { this._maxCacheSize = value; }
}
 internal bool IsSetMaxCacheSize () {
 return this._maxCacheSize.HasValue;
}
 public System.Collections.Generic.List<string> GrantTokens {
 get { return this._grantTokens; }
 set { this._grantTokens = value; }
}
 internal bool IsSetGrantTokens () {
 return this._grantTokens != null;
}
 public void Validate() {
 if (!IsSetBranchKeyId()) throw new System.ArgumentException("Missing value for required property 'BranchKeyId'");
 if (!IsSetKmsKeyId()) throw new System.ArgumentException("Missing value for required property 'KmsKeyId'");
 if (!IsSetKmsClient()) throw new System.ArgumentException("Missing value for required property 'KmsClient'");
 if (!IsSetDdbClient()) throw new System.ArgumentException("Missing value for required property 'DdbClient'");
 if (!IsSetBranchKeysTableName()) throw new System.ArgumentException("Missing value for required property 'BranchKeysTableName'");
 if (!IsSetTtlMilliseconds()) throw new System.ArgumentException("Missing value for required property 'TtlMilliseconds'");

}
}
}
