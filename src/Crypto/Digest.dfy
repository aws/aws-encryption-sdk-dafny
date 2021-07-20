// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Digest {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import DigestAlgo
  import ExternDigest

  function method Length(alg: DigestAlgo.Algorithm): nat {
    match alg
    case SHA_512 => 64
  }

  method Digest(alg: DigestAlgo.Algorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>>)
    ensures res.Success? ==> |res.value| == Length(alg)
  {
    var digest := ExternDigest.Digest(alg, msg);
    if |digest| == Length(alg) {
        return Success(digest);
    } else {
        return Failure("Incorrect length digest from ExternDigest.");
    }
  }
}

module DigestAlgo {
  datatype Algorithm = SHA_512
}

module {:extern "ExternDigest" } ExternDigest {
  import opened UInt = StandardLibrary.UInt
  import opened DigestAlgo = DigestAlgo

  method {:extern } Digest(alg: DigestAlgo.Algorithm, msg: seq<uint8>) returns (digest: seq<uint8>)
}
