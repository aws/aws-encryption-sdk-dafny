// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsKmsTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.Kms"} Com.Amazonaws.Kms refines AbstractComAmazonawsKmsService {

  function method DefaultKMSClientConfigType() : KMSClientConfigType {
    KMSClientConfigType
  }

  /*
   * Returns whether the given client is configured to talk to the given region,
   * or None if the underlying AWS SDK implementation does not support querying the configuration.
   *
   * Useful for MRKs where we need to check whether our client can decrypt an MRK.
   */
  function method {:extern "RegionMatch"} RegionMatch(
    client: IKMSClient,
    region: string
  ): Option<bool>

  method {:extern} KMSClientForRegion(region: string)
    returns (res: Result<IKMSClient, Error>)
    ensures res.Success? ==> 
    && fresh(res.value)
    && fresh(res.value.Modifies)
    && fresh(res.value.History)
    && res.value.ValidState()

}
