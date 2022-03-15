// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "AwsEncryptionSdk.dfy"

module {:extern "Dafny.Aws.EncryptionSdk.AwsEncryptionSdkFactory"} AwsEncryptionSdkFactory {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Esdk
  import AwsEncryptionSdk

  class AwsEncryptionSdkFactory extends Esdk.IAwsEncryptionSdkFactory {

    constructor() {}

    method CreateDefaultAwsEncryptionSdk()
      returns (res: Result<Esdk.IAwsEncryptionSdk, Esdk.IAwsEncryptionSdkException>)

      ensures res.Success?
    {
        var emptyConfig := Esdk.AwsEncryptionSdkConfig(
          commitmentPolicy := None(),
          maxEncryptedDataKeys := None()
        );
        var esdk := new AwsEncryptionSdk.AwsEncryptionSdk(emptyConfig);
        return Success(esdk);
    }

    method CreateAwsEncryptionSdk(input: Esdk.AwsEncryptionSdkConfig)
      returns (res: Result<Esdk.IAwsEncryptionSdk, Esdk.IAwsEncryptionSdkException>)

      ensures
        && input.maxEncryptedDataKeys.Some?
        && input.maxEncryptedDataKeys.value <= 0
      ==>
        res.Failure?

      ensures
        || input.maxEncryptedDataKeys.None?
        || (input.maxEncryptedDataKeys.Some? && input.maxEncryptedDataKeys.value > 0)
      ==>
        res.Success?
    {
        if input.maxEncryptedDataKeys.Some? && input.maxEncryptedDataKeys.value <= 0 {
            var err := new Esdk.AwsEncryptionSdkException("maxEncryptedDataKeys must be non-negative");
            return Failure(err);
        }

        var esdk := new AwsEncryptionSdk.AwsEncryptionSdk(input);
        return Success(esdk);
    }
  }
}
