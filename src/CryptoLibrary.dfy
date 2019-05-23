// =============== Crypto library stuff ===============
include "StandardLibrary.dfy"

module {:extern "Digests"} Digests {
  datatype {:extern "HMAC_ALGORITHM"} HMAC_ALGORITHM = HmacSHA256  | HmacSHA384 | HmacNOSHA
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
  function HashIterate(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, i: nat): seq<byte>
    requires 0 <= i < 256
    decreases i, 1
  {
    if i == 0 then [] else
    Hash(algorithm, key, HashIterateMsg(algorithm, key, info, i))
  }

  // return T(i-1) | info | i
  function HashIterateMsg(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, i: nat): seq<byte>
    requires 1 <= i < 256
    decreases i, 0
  {
    HashIterate(algorithm, key, info, i-1) + info + [WrapIntoByte(i)]
  }
 
  // return T(1) | T(2) | ... | T(n)
  function AccumulatedHashIterates(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, n: nat): seq<byte>
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then [] else
      AccumulatedHashIterates(algorithm, key, info, n-1) + HashIterate(algorithm, key, info, n)
  }
 
  lemma AccHashIterLength(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, n: nat)
    requires 0 <= n < 256
    ensures |AccumulatedHashIterates(algorithm, key, info, n)| == n * HashLength(algorithm)
  {
  }
 
  lemma AccHashIterPrefix(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>, m: nat, n: nat)
    requires 0 <= m <= n < 256
    ensures AccumulatedHashIterates(algorithm, key, info, m) <= AccumulatedHashIterates(algorithm, key, info, n)
  {
    if m == n {
    } else {
      AccHashIterPrefix(algorithm, key, info, m, n-1);
    }
  }
 
  function IteratedHash(algorithm: HMAC_ALGORITHM, key: seq<byte>, info: seq<byte>): (result: seq<byte>)
    ensures |result| == 255 * HashLength(algorithm)
  {
    AccHashIterLength(algorithm, key, info, 255);
    AccumulatedHashIterates(algorithm, key, info, 255)
  }
 
}