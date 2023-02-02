// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsEncryptionSdkTypes.dfy"
include "AwsEncryptionSdkOperations.dfy"

module {:extern "Dafny.qwer.EncryptionSdk" } qwer.EncryptionSdk refines AbstractAwsEncryptionSdkService {
  import Operations = AwsEncryptionSdkOperations
  import Aws.Cryptography.Primitives
  import MaterialProviders
  import AwsCryptographyMaterialProvidersTypes

  function method DefaultAwsEncryptionSdkConfig(): AwsEncryptionSdkConfig
  {
    AwsEncryptionSdkConfig(
      commitmentPolicy := Some(AwsCryptographyMaterialProvidersTypes.REQUIRE_ENCRYPT_REQUIRE_DECRYPT),
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
      commitmentPolicy := config.commitmentPolicy.UnwrapOr(AwsCryptographyMaterialProvidersTypes.REQUIRE_ENCRYPT_REQUIRE_DECRYPT),
      maxEncryptedDataKeys := config.maxEncryptedDataKeys

    );
    var client := new ESDKClient(internalConfig);
    return Success(client);
  }

}
