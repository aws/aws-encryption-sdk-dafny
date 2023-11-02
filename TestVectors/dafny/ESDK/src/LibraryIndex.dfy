// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyEncryptionSdkTypesWrapped.dfy"

module
  {:extern "software.amazon.cryptography.encryptionsdk.internaldafny.wrapped" }
  WrappedESDK refines WrappedAbstractAwsCryptographyEncryptionSdkService
{
  import WrappedService = EncryptionSdk

  function method WrappedDefaultAwsEncryptionSdkConfig(): AwsEncryptionSdkConfig
  {
    AwsEncryptionSdkConfig(
      commitmentPolicy := Some(AwsCryptographyMaterialProvidersTypes.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT),
      maxEncryptedDataKeys := None
    )
  }

  function method WrappedAwsEncryptionSdkConfigWithSuppliedCommitment(
    commitmentPolicy: AwsCryptographyMaterialProvidersTypes.ESDKCommitmentPolicy
  ): AwsEncryptionSdkConfig
  {
    AwsEncryptionSdkConfig(
      commitmentPolicy := Some(commitmentPolicy),
      maxEncryptedDataKeys := None
    )
  }
}