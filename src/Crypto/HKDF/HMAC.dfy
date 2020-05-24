// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../KeyDerivationAlgorithms.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened KeyDerivationAlgorithms
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype {:extern "Digests"} Digests = SHA_256 | SHA_384

  // Hash length in octets (bytes), e.g. GetHashLength(SHA_256) ==> 256 bits = 32 bytes ==> n = 32
  function method GetHashLength(digest: Digests): int
  {
    match digest
    case SHA_256 => 32
    case SHA_384 => 48
  }

  class {:extern "HMac"} HMac {

    // These functions are used to model the extern state
    // https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
    function {:extern} GetKey(): seq<uint8> reads this
    function {:extern} GetDigest(): Digests reads this
    function {:extern} GetInputSoFar(): seq<uint8> reads this

    constructor {:extern} (digest: Digests)
      ensures this.GetDigest() == digest
      ensures this.GetInputSoFar() == []

    method {:extern "Init"} Init(key: seq<uint8>)
      modifies this
      ensures this.GetKey() == key;
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetInputSoFar() == []

    method {:extern "BlockUpdate"} Update(input: seq<uint8>)
      requires |this.GetKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.GetInputSoFar() == old(this.GetInputSoFar()) + input
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())

    method {:extern "GetResult"} GetResult() returns (s: seq<uint8>)
      requires |this.GetKey()| > 0
      modifies this
      ensures |s| == GetHashLength(this.GetDigest())
      ensures this.GetInputSoFar() == []
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      ensures this.HashSignature(old(this.GetInputSoFar()), s);

    predicate {:axiom} HashSignature(message: seq<uint8>, s: seq<uint8>)

  }
}
