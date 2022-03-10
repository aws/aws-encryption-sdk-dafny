// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "AwsEncryptionSdk.dfy"

module {:extern "Dafny.Aws.Esdk.AwsEncryptionSdkClientFactory"} AwsEncryptionSdkClientFactory {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Esdk
  import AwsEncryptionSdk

  class AwsEncryptionSdkClientFactory extends Esdk.IAwsEncryptionSdkClientFactory {

    constructor() {}

    method CreateDefaultAwsEncryptionSdkClient()
      returns (res: Result<Esdk.IAwsEncryptionSdkClient, Esdk.IAwsEncryptionSdkException>)

      ensures res.Success?
    {
        var emptyConfig := Esdk.AwsEncryptionSdkClientConfig(
          commitmentPolicy := None(),
          maxEncryptedDataKeys := None()
        );
        var esdk := new AwsEncryptionSdk.AwsEncryptionSdkClient(emptyConfig);
        return Success(esdk);
    }

    method CreateAwsEncryptionSdkClient(input: Esdk.AwsEncryptionSdkClientConfig)
      returns (res: Result<Esdk.IAwsEncryptionSdkClient, Esdk.IAwsEncryptionSdkException>)

      ensures
        && input.maxEncryptedDataKeys.Some?
        && input.maxEncryptedDataKeys.value < 0 // TODO: Change to '<= 0' once CrypTool-4350 complete
      ==>
        res.Failure?

      ensures
        || input.maxEncryptedDataKeys.None?
        || (input.maxEncryptedDataKeys.Some? && input.maxEncryptedDataKeys.value >= 0) // TODO: Change to '> 0' once CrypTool-4350 complete
      ==>
        res.Success?
    {
        // TODO Use :- Need(...) once exception types play nice
        // TODO: Change to '<= 0' once CrypTool-4350 complete
        if input.maxEncryptedDataKeys.Some? && input.maxEncryptedDataKeys.value < 0 {
            var err := new Esdk.AwsEncryptionSdkClientException("maxEncryptedDataKeys must be non-negative");
            return Failure(err);
        }

        var esdk := new AwsEncryptionSdk.AwsEncryptionSdkClient(input);
        return Success(esdk);
    }
  }
}
