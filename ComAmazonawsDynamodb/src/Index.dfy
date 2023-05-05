// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsDynamodbTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.Dynamodb"} Com.Amazonaws.Dynamodb refines AbstractComAmazonawsDynamodbService {

  function method DefaultDynamoDBClientConfigType() : DynamoDBClientConfigType {
    DynamoDBClientConfigType
  }

  method {:extern} DDBClientForRegion(region: string)
    returns (res: Result<IDynamoDBClient, Error>)
    ensures res.Success? ==>
      && fresh(res.value)
      && fresh(res.value.Modifies)
      && fresh(res.value.History)
      && res.value.ValidState()
}
