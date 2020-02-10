include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Digests"} Digests {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // See Key Derivation Algorithm
  // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/algorithms-reference.html
  datatype {:extern "KeyDerivationAlgorithm"} KeyDerivationAlgorithm = HKDF_WITH_SHA_384 | HKDF_WITH_SHA_256 | IDENTITY

  // Hash length in octets (bytes), e.g. HashLength(SHA256) = 256 = 32 * 8
  function HashLength(algorithm: KeyDerivationAlgorithm): (n: int32)
    ensures algorithm == HKDF_WITH_SHA_256 ==> n == 32
    ensures algorithm == HKDF_WITH_SHA_384 ==> n == 48
    ensures algorithm == IDENTITY ==> n == 0
  {
    match algorithm {
      case HKDF_WITH_SHA_256 => 32
      case HKDF_WITH_SHA_384 => 48
      case IDENTITY => 0
    }
  }

    function {:axiom} Hash(algorithm: KeyDerivationAlgorithm, key: seq<uint8>, message: seq<uint8>): (s: seq<uint8>)
      ensures |s| == HashLength(algorithm) as int
}
