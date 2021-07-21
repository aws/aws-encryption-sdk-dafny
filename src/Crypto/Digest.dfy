// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Digest {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Hash
  import ExternDigest

  function method Length(alg: Hash.Algorithm): nat {
    match alg
    case SHA_512 => 64
  }

  method Digest(alg: Hash.Algorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>>)
    ensures res.Success? ==> |res.value| == Length(alg)
  {
    var digest := ExternDigest.Digest(alg, msg);
    return digest;
  }
}

module Hash {
  datatype Algorithm = SHA_512
}

module {:extern "ExternDigest" } ExternDigest {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Hash

  method {:extern } Digest(alg: Hash.Algorithm, msg: seq<uint8>) returns (digest: Result<seq<uint8>>)
    ensures res.Success? ==> |res.value| == Length(alg)
}
