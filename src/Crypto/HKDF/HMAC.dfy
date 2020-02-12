include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened Digests
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype {:extern "CipherParameters"} CipherParameters = KeyParameter(key: seq<uint8>)

  // Hash length in octets (bytes), e.g. GetHashLength(SHA256) ==> 256 bits = 32 bytes ==> n = 32
  function method GetHashLength(algorithm: KeyDerivationAlgorithm): (n: int32)
    requires algorithm != IDENTITY
    ensures algorithm == HKDF_WITH_SHA_256 ==> n == 32
    ensures algorithm == HKDF_WITH_SHA_384 ==> n == 48
  {
    match algorithm {
      case HKDF_WITH_SHA_256 => 32
      case HKDF_WITH_SHA_384 => 48
    }
  }

  class {:extern "HMac"} HMac {

    ghost var initialized: Option<seq<uint8>>

    constructor {:extern} (algorithm: KeyDerivationAlgorithm)
      requires algorithm != IDENTITY

    predicate {:axiom} ValidKey(key: seq<uint8>)

    method {:extern "Init"} Init(params: CipherParameters)
      requires params.KeyParameter?
      ensures
        var key := match params case KeyParameter(key) => key;
        match initialized { case Some(k) => ValidKey(k) && key == k case None => false }

    method {:extern "Update"} UpdateSingle(input: uint8)
      requires initialized.Some?

    method {:extern "BlockUpdate"} Update(input: seq<uint8>, inOff: int32, len: int32)
      requires initialized.Some?
      requires inOff >= 0
      requires len >= 0
      requires |input| < INT32_MAX_LIMIT
      requires inOff as int + len as int <= |input|

    method {:extern "GetResult"} GetResult() returns (s: seq<uint8>)
      requires initialized.Some?
  }
}
