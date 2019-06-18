// =============== Crypto library stuff ===============
include "StandardLibrary.dfy"

module {:extern "Digests"} Digests {
  datatype {:extern "HMAC_ALGORITHM"} HMAC_ALGORITHM = HmacSHA256 | HmacSHA384 | HmacNOSHA
}

module HKDFSpec {
  import opened StandardLibrary
  import opened Digests
  
  // Hash length in octets, e.g. HashLength(SHA256) = 256 = 32 * 8
  function {:axiom} HashLength(algorithm: HMAC_ALGORITHM): nat
    ensures algorithm == HmacSHA256 ==> HashLength(algorithm) == 32
    ensures algorithm == HmacSHA384 ==> HashLength(algorithm) == 48

  function {:axiom} Hash(algorithm: HMAC_ALGORITHM, key: seq<byte>, message: seq<byte>): seq<byte>
    ensures |Hash(algorithm, key, message)| == HashLength(algorithm)

  // return T(i)
  function Ti(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, i: nat): seq<byte>
    requires 0 <= i < 256
    decreases i, 1
  {
    if i == 0 then [] else
    Hash(algorithm, key, PreTi(algorithm, key, info, i))
  }

  // return T(i-1) | info | i
  function PreTi(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, i: nat): seq<byte>
    requires 1 <= i < 256
    decreases i, 0
  {
    Ti(algorithm, key, info, i-1) + info + [(i as byte)]
  }
 
  // return T(1) | T(2) | ... | T(n)
  function T(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, n: nat): seq<byte>
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then [] else
      T(algorithm, key, info, n-1) + Ti(algorithm, key, info, n)
  }
 
  lemma TLength(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, n: nat)
    requires 0 <= n < 256
    ensures |T(algorithm, key, info, n)| == n * HashLength(algorithm)
  {
  }
 
  lemma TPrefix(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, m: nat, n: nat)
    requires 0 <= m <= n < 256
    ensures T(algorithm, key, info, m) <= T(algorithm, key, info, n)
  {
    if m == n {
    } else {
      TPrefix(algorithm, key, info, m, n-1);
    }
  }
 
  function TMaxLength(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>): (result: seq<byte>)
    ensures |result| == 255 * HashLength(algorithm)
  {
    TLength(algorithm, key, info, 255);
    T(algorithm, key, info, 255)
  }
 
}