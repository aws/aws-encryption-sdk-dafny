// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AwsEncryptionSdkOperations.dfy"

module 
  {:extern "software.amazon.cryptography.encryptionsdk.internaldafny" }
  EncryptionSdk refines AbstractAwsCryptographyEncryptionSdkService {
  import Operations = AwsEncryptionSdkOperations
  import Aws.Cryptography.Primitives
  import MaterialProviders
  import AwsCryptographyMaterialProvidersTypes

  function method DefaultAwsEncryptionSdkConfig(): AwsEncryptionSdkConfig
  {
    AwsEncryptionSdkConfig(
      commitmentPolicy := Some(AwsCryptographyMaterialProvidersTypes.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT),
      maxEncryptedDataKeys := None
    )
  }

  method ESDK(config: AwsEncryptionSdkConfig)
    returns (res: Result<ESDKClient, Error>)
  {
    var maybeCrypto := Primitives.AtomicPrimitives();
    var crypto :- maybeCrypto
      .MapFailure(e => AwsCryptographyPrimitives(e));

    var maybeMpl := MaterialProviders.MaterialProviders();
    var mpl :- maybeMpl
      .MapFailure(e => AwsCryptographyMaterialProviders(e));
    var internalConfig := Operations.Config(
      crypto := crypto,
      mpl := mpl,
      commitmentPolicy := config.commitmentPolicy.UnwrapOr(AwsCryptographyMaterialProvidersTypes.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT),
      maxEncryptedDataKeys := config.maxEncryptedDataKeys

    );
    var client := new ESDKClient(internalConfig);
    return Success(client);
  }

  class ESDKClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IAwsEncryptionSdkClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
