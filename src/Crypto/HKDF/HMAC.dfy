include "../KeyDerivationAlgorithms.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened KeyDerivationAlgorithms
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // Hash length in octets (bytes), e.g. GetHashLength(SHA256) ==> 256 bits = 32 bytes ==> n = 32
  function method GetHashLength(algorithm: HKDFAlgorithms): (n: int32)
    ensures algorithm == HKDF_WITH_SHA_256 ==> n == 32
    ensures algorithm == HKDF_WITH_SHA_384 ==> n == 48
  {
    match algorithm {
      case HKDF_WITH_SHA_256 => 32
      case HKDF_WITH_SHA_384 => 48
    }
  }

  class {:extern "HMac"} HMac {

    // These functions are used to model the extern state
    // https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
    function {:extern} getKey(): seq<uint8> reads this
    function {:extern} getAlgorithm(): HKDFAlgorithms reads this
    function {:extern} getInputSoFar(): seq<uint8> reads this

    constructor {:extern} (algorithm: HKDFAlgorithms)
      ensures this.getAlgorithm() == algorithm
      ensures this.getInputSoFar() == []

    method {:extern "Init"} Init(key: seq<uint8>)
      modifies this
      ensures this.getKey() == key;
      ensures this.getAlgorithm() == old(this.getAlgorithm())
      ensures this.getInputSoFar() == []

    method {:extern "BlockUpdate"} Update(input: seq<uint8>)
      requires |this.getKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.getInputSoFar() == old(this.getInputSoFar()) + input
      ensures this.getAlgorithm() == old(this.getAlgorithm())
      ensures this.getKey() == old(this.getKey())

    method {:extern "GetResult"} GetResult() returns (s: seq<uint8>)
      requires |this.getKey()| > 0
      modifies this
      ensures |s| == GetHashLength(this.getAlgorithm()) as int
      ensures this.getInputSoFar() == []
      ensures this.getAlgorithm() == old(this.getAlgorithm())
      ensures this.getKey() == old(this.getKey())
  }
}
