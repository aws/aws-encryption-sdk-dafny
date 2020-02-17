include "HMAC.dfy"
include "../KeyDerivationAlgorithms.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

 /*
  * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
  */
module HKDF {
  import opened HMAC
  import opened KeyDerivationAlgorithms
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>, ghost algorithm: HKDFAlgorithms) returns (prk: seq<uint8>)
    requires hmac.getAlgorithm() == algorithm
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures GetHashLength(hmac.getAlgorithm()) as int == |prk|
    ensures hmac.getKey() == salt
    ensures hmac.getAlgorithm() == algorithm
  {
    // prk = HMAC-Hash(salt, ikm)
    hmac.Init(salt);
    hmac.Update(ikm);
    assert hmac.getInputSoFar() == ikm;

    prk := hmac.GetResult();
    return prk;
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, expectedLength: int, algorithm: HKDFAlgorithms, ghost salt: seq<uint8>) returns (okm: seq<uint8>)
    requires hmac.getAlgorithm() == algorithm
    requires 1 <= expectedLength <= 255 * GetHashLength(hmac.getAlgorithm()) as int
    requires |salt| != 0
    requires hmac.getKey() == salt
    requires |info| < INT32_MAX_LIMIT
    requires GetHashLength(hmac.getAlgorithm()) as int == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.getKey() == prk
  {
    // N = ceil(L / Hash Length)
    var hashLength := GetHashLength(algorithm);
    var n := 1 + (expectedLength - 1) / hashLength as int;

    // T(0) = empty string (zero length)
    hmac.Init(prk);
    var t_last := [];
    var t_n := t_last;

    // T = T(0) + T (1) + T(2) + ... T(n)
    // T(1) = HMAC-Hash(PRK, T(1) | info | 0x01)
    // ...
    // T(n) = HMAC-Hash(prk, T(n - 1) | info | 0x0n)
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant i == 1 ==> |t_last| == 0
      invariant i > 1 ==> |t_last| == hashLength as int
      invariant hashLength as int == |prk|
      invariant |t_n| == (i - 1) * hashLength as int;
      invariant hmac.getKey() == prk
      invariant hmac.getAlgorithm() == algorithm
      invariant hmac.getInputSoFar() == []
    {
      hmac.Update(t_last);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.getInputSoFar() == t_last + info + [(i as uint8)];

      // Add additional verification for T(n): github.com/awslabs/aws-encryption-sdk-dafny/issues/177
      t_last := hmac.GetResult();
      t_n := t_n + t_last;
      i := i + 1;
    }

    // okm = first L bytes of T(n)
    okm := t_n;
    if |okm| > expectedLength {
      okm := okm[..expectedLength];
    }
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(algorithm: HKDFAlgorithms, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int) returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * GetHashLength(algorithm) as int
    requires salt.None? || |salt.get| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
  {
    if L == 0 {
      return [];
    }
    var hmac := new HMac(algorithm);
    var hashLength := GetHashLength(algorithm);

    var saltNonEmpty: seq<uint8>;
    match salt {
      case None =>
        saltNonEmpty := Fill(0, hashLength as int);
      case Some(s) =>
        saltNonEmpty := s;
    }

    var prk := Extract(hmac, saltNonEmpty, ikm, algorithm);
    okm := Expand(hmac, prk, info, L, algorithm, saltNonEmpty);
  }
}
