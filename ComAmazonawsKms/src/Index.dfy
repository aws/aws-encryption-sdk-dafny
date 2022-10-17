// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsKmsTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.Kms"} Com.Amazonaws.Kms refines AbstractComAmazonawsKmsService {

  function method DefaultKMSClientConfigType() : KMSClientConfigType {
    KMSClientConfigType
  }

}
