include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module HKDFSpec {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Digests

  // return T(i)
  function Ti(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, i: nat): seq<uint8>
    requires 0 <= i < 256
    requires HashLength(algorithm) <= |key|
    decreases i, 1
  {
    if i == 0 then [] else
    Hash(algorithm, key, PreTi(algorithm, key, info, i))
  }

  // return T(i-1) | info | i
  function PreTi(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, i: nat): seq<uint8>
    requires 1 <= i < 256
    requires HashLength(algorithm) <= |key|
    decreases i, 0
  {
    Ti(algorithm, key, info, i-1) + info + [(i as uint8)]
  }
 
  // return T(1) | T(2) | ... | T(n)
  function T(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, n: nat): seq<uint8>
    requires 0 <= n < 256
    requires HashLength(algorithm) <= |key|
    decreases n
  {
    if n == 0 then [] else
      T(algorithm, key, info, n-1) + Ti(algorithm, key, info, n)
  }
 
  lemma TLength(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, n: nat)
    requires 0 <= n < 256
    requires HashLength(algorithm) <= |key|
    ensures |T(algorithm, key, info, n)| == n * HashLength(algorithm)
  {
  }
 
  lemma TPrefix(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, m: nat, n: nat)
    requires 0 <= m <= n < 256
    requires HashLength(algorithm) <= |key|
    ensures T(algorithm, key, info, m) <= T(algorithm, key, info, n)
  {
    if m == n {
    } else {
      TPrefix(algorithm, key, info, m, n-1);
    }
  }
 
  function TMaxLength(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>): (result: seq<uint8>)
    requires HashLength(algorithm) <= |key|
    ensures |result| == 255 * HashLength(algorithm)
  {
    TLength(algorithm, key, info, 255);
    T(algorithm, key, info, 255)
  }
 
}