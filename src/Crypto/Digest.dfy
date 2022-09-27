// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./Datatypes.dfy"

module Digest {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import CryptoDatatypes
  import ExternDigest

  function method Length(alg: CryptoDatatypes.DigestAlgorithm): nat {
    match alg
    case SHA_512 => 64
  }

  method Digest(alg: CryptoDatatypes.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, string>)
    ensures res.Success? ==> |res.value| == Length(alg)
  {
    var result := ExternDigest.Digest(alg, msg);
    if result.Success? && |result.value| != Length(alg) {
      return Failure("Incorrect length digest from ExternDigest.");
    }
    return result;
  }
}

module {:extern "ExternDigest" } ExternDigest {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened CryptoDatatypes

  method {:extern } Digest(alg: CryptoDatatypes.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, string>)
}
