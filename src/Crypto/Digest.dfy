include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module {:extern "Digest"} Digest {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype Algorithm = SHA_512

  method {:extern "Digest.SHA", "Digest"} Digest(alg: Algorithm, msg: seq<uint8>) returns (digest: Result<seq<uint8>>)
}
