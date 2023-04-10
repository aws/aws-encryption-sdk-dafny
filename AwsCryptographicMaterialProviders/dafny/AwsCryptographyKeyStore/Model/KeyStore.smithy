// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace aws.cryptography.keyStore

// The top level namespace for this project.
// Contains an entry-point for helper methods,
// and common structures used throughout this project.

use aws.polymorph#localService
use aws.polymorph#reference
use aws.polymorph#extendable

use com.amazonaws.dynamodb#TableName
use com.amazonaws.dynamodb#TableArn

@localService(
  sdkId: "KeyStore",
  config: KeyStoreConfig,
)
service KeyStore {
  version: "2023-04-01",
  operations: [
    CreateKeyStore,
    CreateKey,
    VersionKey,
    GetActiveBranchKey,
    GetBranchKeyVersion,
    GetBeaconKey
  ],
  errors: [KeyStoreException]
}

structure KeyStoreConfig {
  ddbTableName: TableName,
  ddbClient: aws.cryptography.materialProviders#DdbClientReference,
  kmsClient: aws.cryptography.materialProviders#KmsClientReference,
}

operation CreateKeyStore {
  input: CreateKeyStoreInput,
  output: CreateKeyStoreOutput
}

structure CreateKeyStoreInput {
}

structure CreateKeyStoreOutput {
}

// CreateKey will create two keys to add to the key store
// One is the branch key, which is used in the hierarchical keyring
// The second is a beacon key that is used as a root key to
// derive different beacon keys per beacon.
operation CreateKey {
  input: CreateKeyInput,
  output: CreateKeyOutput
}

structure CreateKeyInput {
  @required
  awsKmsKeyArn: aws.cryptography.materialProviders#KmsKeyId,
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
  branchKeyIdentifier: String,
}

operation GetActiveBranchKey {
  input: GetActiveBranchKeyInput,
  output: GetActiveBranchKeyOutput
}

structure GetActiveBranchKeyInput {
  @required
  branchKeyIdentifier: String,

  awsKmsKeyArn: aws.cryptography.materialProviders#KmsKeyId
}

structure GetActiveBranchKeyOutput {
  @required
  branchKey: aws.cryptography.materialProviders#Secret,

  @required
  branchKeyVersion: String,
  
  awsKmsKeyArn: aws.cryptography.materialProviders#KmsKeyId
}

operation GetBranchKeyVersion {
  input: GetBranchKeyVersionInput,
  output: GetBranchKeyVersionOutput
}

structure GetBranchKeyVersionInput {
  @required
  branchKeyIdentifier: String,

  @required
  branchKeyVersion: String,
  
  awsKmsKeyArn: aws.cryptography.materialProviders#KmsKeyId
}

structure GetBranchKeyVersionOutput {
  @required
  branchKey: aws.cryptography.materialProviders#Secret,

  @required
  branchKeyVersion: String
}

operation GetBeaconKey {
  input: GetBeaconKeyInput,
  output: GetBeaconKeyOutput
}

structure GetBeaconKeyInput {
  @required
  branchKeyIdentifier: String,
  
  awsKmsKeyArn: aws.cryptography.materialProviders#KmsKeyId
}

structure GetBeaconKeyOutput {
  @required
  beaconKey: aws.cryptography.materialProviders#Secret 
}

///////////////////
// Errors

@error("client")
structure KeyStoreException {
  @required
  message: String,
}
