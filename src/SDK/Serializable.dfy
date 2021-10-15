// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"

module Serializable {
  import opened UInt = StandardLibrary.UInt

  type UINT16Seq = i: seq<uint8> | |i| < UINT16_LIMIT
    witness *
  type UINT32Seq = i: seq<uint8> | |i| < UINT32_LIMIT
    witness *

}
