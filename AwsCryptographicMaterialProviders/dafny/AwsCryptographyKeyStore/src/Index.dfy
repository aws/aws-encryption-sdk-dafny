// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "AwsCryptographyKeyStoreOperations.dfy"

module {:extern "Dafny.Aws.Cryptography.KeyStore"}
  KeyStore refines AbstractAwsCryptographyKeyStoreService
{
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
      ddbTableName := None,
      kmsClient := None,
      ddbClient := None
    )
  }

  method KeyStore(config: KeyStoreConfig)
    returns (res: Result<KeyStoreClient, Error>)
  {
    :- Need(
      && config.ddbTableName.Some?
      && config.kmsClient.Some?
      && config.ddbClient.Some?,
      Types.KeyStoreException(
        message := "MUST supply Amazon DynamoDB Table Name, AWS KMS Client, and Amazon DynamoDB Client")
    );

    
    var keyStoreId :- if config.id.Some? then
      Success(config.id.value)
    else
      UUID.GenerateUUID().MapFailure(e => Types.KeyStoreException(message := e));

    var client := new KeyStoreClient(
      Operations.Config(
        id := keyStoreId,
        ddbTableName := config.ddbTableName.value,
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