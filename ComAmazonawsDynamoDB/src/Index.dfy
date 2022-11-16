// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../model/ComAmazonawsDynamodbTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.DynamoDB"} Com.Amazonaws.DynamoDB refines ComAmazonawsDynamodbAbstract {

  function method DefaultDynamoDBClientConfigType() : DynamoDBClientConfigType {
    DynamoDBClientConfigType
  }

}
