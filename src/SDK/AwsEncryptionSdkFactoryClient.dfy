// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// TODO: Originally written as part of POC; we should come back through this
// to refine it

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "AwsEncryptionSdk.dfy"

module {:extern "Dafny.Aws.Esdk.AwsEncryptionSdkFactoryClient"} AwsEncryptionSdkFactoryClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Esdk
  import AwsEncryptionSdk

  class AwsEncryptionSdkFactoryClient extends Esdk.IAwsEncryptionSdkFactoryClient {

    constructor() {}

    method MakeAwsEncryptionSdk(input: Esdk.AwsEncryptionSdkClientConfig)
      returns (res: Result<Esdk.IAwsEncryptionSdkClient, Esdk.IAwsEncryptionSdkFactoryException>)

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

      // TODO it seems natural to want to be able to verify the below, however since things like maxEncryptedDataKeys and commitmentPolicy
      // are not defined on the interface, they cannot be. Thus it seems to be difficult for this method to produce a client
      // that has all the verified goodness which may be needed. This doesn't appear to be an issue now, but could potentially block
      // efforts to prove things about the client produced by this method.
      // ensures res.Success? ==>
      //   && res.value.config == input
      //   && res.value.maxEncryptedDataKeys == input.maxEncryptedDataKeys
      // ensures res.Success? && config.commitmentPolicy.None? ==>
      //   && var policy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
      //   && res.commitmentPolicy == policy
      // ensures res.Success? && config.commitmentPolicy.Some? ==>
      //   && res.commitmentPolicy == config.commitmentPolicy.value          
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
