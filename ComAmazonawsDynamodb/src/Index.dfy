// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsDynamodbTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.Dynamodb"} Com.Amazonaws.Dynamodb refines AbstractComAmazonawsDynamodbService {

  function method DefaultDynamoDBClientConfigType() : DynamoDBClientConfigType {
    DynamoDBClientConfigType
  }

}
