// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "AwsCryptographyKeyStoreOperations.dfy"
include "../../../dafny/AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"

module {:extern "Dafny.Aws.Cryptography.KeyStore"}
  KeyStore refines AbstractAwsCryptographyKeyStoreService
{
  import opened AwsArnParsing
  import Operations = AwsCryptographyKeyStoreOperations
  import Com.Amazonaws.Kms
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import UUID

  // TODO there is no sensible default, so what should this do?
  // As is, the default config is invalid. Can we update the codegen to *not*
  // build a default config?
  function method DefaultKeyStoreConfig(): KeyStoreConfig
  {
    KeyStoreConfig(
      id := None,
      ddbTableName := "None",
      kmsKeyArn := "",
      kmsClient := None,
      ddbClient := None
    )
  }

  method KeyStore(config: KeyStoreConfig)
    returns (res: Result<KeyStoreClient, Error>)
    ensures res.Success? ==>
      && KMS.IsValid_KeyIdType(res.value.config.kmsKeyArn)
      && DDB.IsValid_TableName(config.ddbTableName)
      && config.kmsClient.Some?
      && config.ddbClient.Some?
      && res.value.config.kmsClient == config.kmsClient.value
      && res.value.config.ddbClient == config.ddbClient.value
    ensures
        && config.kmsClient.None?
        && config.ddbClient.None?
        && !DDB.IsValid_TableName(config.ddbTableName)
        && !KMS.IsValid_KeyIdType(config.kmsKeyArn)
        && ParseAwsKmsArn(config.kmsKeyArn).Failure?
      ==>
        res.Failure?
  {
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#initialization
    //# The following inputs MUST be specified to create a KeyStore:
    :- Need(
      && config.kmsClient.Some?
      && config.ddbClient.Some?,
      Types.KeyStoreException(
        message := "MUST supply AWS KMS Client, and Amazon DynamoDB Client")
    );
    :- Need(
      DDB.IsValid_TableName(config.ddbTableName),
      Types.KeyStoreException(
        message := "Invalid Amazon DynamoDB Table Name")
    );
    
    :- Need(
      && KMS.IsValid_KeyIdType(config.kmsKeyArn)
      && ParseAwsKmsArn(config.kmsKeyArn).Success?,
      Types.KeyStoreException(
        message := "Invalid AWS KMS Key Arn")
    );

    var keyStoreId;

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#initialization
    //# The following inputs MAY be specified to create a KeyStore:
    if config.id.Some? {
      keyStoreId := config.id.value;
    } else {
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#key-store-id
      //# If one is not supplied, then a [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt) MUST be used.
      var maybeUuid := UUID.GenerateUUID();
      var uuid :- maybeUuid
        .MapFailure(e => Types.KeyStoreException(message := e));
      keyStoreId := uuid;
    }

    var client := new KeyStoreClient(
      Operations.Config(
        id := keyStoreId,
        ddbTableName := config.ddbTableName,
        kmsKeyArn := config.kmsKeyArn,
        kmsClient := config.kmsClient.value,
        ddbClient := config.ddbClient.value
      )
    );
    return Success(client);
  }

  class KeyStoreClient... {
    
    predicate {:vcs_split_on_every_assert} {:rlimit 3000} ValidState() {
      && Operations.ValidInternalConfig?(config)
      && History !in Operations.ModifiesInternalConfig(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IKeyStoreClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}