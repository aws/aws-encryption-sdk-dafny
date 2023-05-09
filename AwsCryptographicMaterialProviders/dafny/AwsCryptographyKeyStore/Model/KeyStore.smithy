// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace aws.cryptography.keyStore

// The top level namespace for this project.
// Contains an entry-point for helper methods,
// and common structures used throughout this project.

use aws.polymorph#localService
use aws.polymorph#reference
use aws.polymorph#extendable
use aws.polymorph#dafnyUtf8Bytes

use com.amazonaws.dynamodb#TableName
use com.amazonaws.dynamodb#TableArn
use com.amazonaws.dynamodb#DynamoDB_20120810

use com.amazonaws.kms#TrentService


@dafnyUtf8Bytes
string Utf8Bytes

@reference(service: TrentService)
structure KmsClientReference {}

@reference(service: DynamoDB_20120810)
structure DdbClientReference {}

@localService(
  sdkId: "KeyStore",
  config: KeyStoreConfig,
  dependencies: [
    DynamoDB_20120810,
    TrentService
  ] 
)
service KeyStore {
  version: "2023-04-01",
  operations: [
    GetKeyStoreInfo,
    CreateKeyStore,
    CreateKey,
    VersionKey,
    GetActiveBranchKey,
    GetBranchKeyVersion,
    GetBeaconKey,
    BranchKeyStatusResolution
  ],
  errors: [KeyStoreException]
}

structure KeyStoreConfig {
  @required
  ddbTableName: TableName,
  @required
  kmsConfiguration: KMSConfiguration,
  @required
  logicalKeyStoreName: String,
  
  id: String,
  grantTokens: GrantTokenList,
  ddbClient: DdbClientReference,
  kmsClient: KmsClientReference,
}

union KMSConfiguration {
  kmsKeyArn: KmsKeyArn
}

operation GetKeyStoreInfo {
  output: GetKeyStoreInfoOutput
}

structure GetKeyStoreInfoOutput {
  @required
  keyStoreId: String,
  @required
  keyStoreName: TableName,
  @required
  logicalKeyStoreName: String,
  @required
  grantTokens: GrantTokenList,
  @required
  kmsConfiguration: KMSConfiguration
}

operation CreateKeyStore {
  input: CreateKeyStoreInput,
  output: CreateKeyStoreOutput
}

structure CreateKeyStoreInput {
}

structure CreateKeyStoreOutput {
  @required
  tableArn: com.amazonaws.dynamodb#TableArn
}

// CreateKey will create two keys to add to the key store
// One is the branch key, which is used in the hierarchical keyring
// The second is a beacon key that is used as a root key to
// derive different beacon keys per beacon.
operation CreateKey {
  output: CreateKeyOutput
}

structure CreateKeyOutput {
  @required
  branchKeyIdentifier: String
}

// VersionKey will create a new branch key under the 
// provided branchKeyIdentifier and rotate the "older" material 
// on the key store under the branchKeyIdentifier. This operation MUST NOT
// rotate the beacon key under the branchKeyIdentifier.
operation VersionKey {
  input: VersionKeyInput
}

structure VersionKeyInput {
  @required
  branchKeyIdentifier: String
}

operation GetActiveBranchKey {
  input: GetActiveBranchKeyInput,
  output: GetActiveBranchKeyOutput
}

structure GetActiveBranchKeyInput {
  @required
  branchKeyIdentifier: String
}

structure GetActiveBranchKeyOutput {
  @required
  branchKeyVersion: Utf8Bytes,

  @required
  branchKey: Secret
}

operation GetBranchKeyVersion {
  input: GetBranchKeyVersionInput,
  output: GetBranchKeyVersionOutput
}

structure GetBranchKeyVersionInput {
  @required
  branchKeyIdentifier: String,

  @required
  branchKeyVersion: String
}

structure GetBranchKeyVersionOutput {
  @required
  branchKeyVersion: Utf8Bytes,

  @required
  branchKey: Secret
}

operation GetBeaconKey {
  input: GetBeaconKeyInput,
  output: GetBeaconKeyOutput
}

structure GetBeaconKeyInput {
  @required
  branchKeyIdentifier: String
}

structure GetBeaconKeyOutput {
  @required
  beaconKeyIdentifier: String,

  @required
  beaconKey: Secret,
}

operation BranchKeyStatusResolution {
  input: BranchKeyStatusResolutionInput
}

structure BranchKeyStatusResolutionInput {
  @required
  branchKeyIdentifier: String
}

string KmsKeyArn

list GrantTokenList {
  member: String
}

@sensitive
blob Secret

///////////////////
// Errors

@error("client")
structure KeyStoreException {
  @required
  message: String,
}
