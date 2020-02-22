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

  function method GetHMACDigestFromHKDFAlgorithm(algorithm: HKDFAlgorithms): Digests
  {
    match algorithm
    case HKDF_WITH_SHA_256 => SHA_256
    case HKDF_WITH_SHA_384 => SHA_384
  }

  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>, ghost digest: Digests) returns (prk: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures GetHashLength(hmac.GetDigest()) == |prk|
    ensures hmac.GetKey() == salt
    ensures hmac.GetDigest() == digest
  {
    // prk = HMAC-Hash(salt, ikm)
    hmac.Init(salt);
    hmac.Update(ikm);
    assert hmac.GetInputSoFar() == ikm;

    prk := hmac.GetResult();
    return prk;
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, expectedLength: int, digest: Digests, ghost salt: seq<uint8>) returns (okm: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires 1 <= expectedLength <= 255 * GetHashLength(hmac.GetDigest())
    requires |salt| != 0
    requires hmac.GetKey() == salt
    requires |info| < INT32_MAX_LIMIT
    requires GetHashLength(hmac.GetDigest()) == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.GetKey() == prk
  {
    // N = ceil(L / Hash Length)
    var hashLength := GetHashLength(digest);
    var n := (hashLength + expectedLength - 1) / hashLength;

    // T(0) = empty string (zero length)
    hmac.Init(prk);
    var t_prev := [];
    var t_n := t_prev;

    // T = T(0) + T (1) + T(2) + ... T(n)
    // T(1) = HMAC-Hash(PRK, T(1) | info | 0x01)
    // ...
    // T(n) = HMAC-Hash(prk, T(n - 1) | info | 0x0n)
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |t_prev| == if i == 1 then 0 else hashLength
      invariant hashLength == |prk|
      invariant |t_n| == (i - 1) * hashLength
      invariant hmac.GetKey() == prk
      invariant hmac.GetDigest() == digest
      invariant hmac.GetInputSoFar() == []
    {
      hmac.Update(t_prev);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.GetInputSoFar() == t_prev + info + [i as uint8];

      // Add additional verification for T(n): github.com/awslabs/aws-encryption-sdk-dafny/issues/177
      t_prev := hmac.GetResult();
      t_n := t_n + t_prev;
      i := i + 1;
    }

    // okm = first L (expectedLength) bytes of T(n)
    okm := t_n;
    if |okm| > expectedLength {
      okm := okm[..expectedLength];
    }
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(algorithm: HKDFAlgorithms, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int) returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * GetHashLength(GetHMACDigestFromHKDFAlgorithm(algorithm))
    requires salt.None? || |salt.get| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
  {
    if L == 0 {
      return [];
    }
    var digest := GetHMACDigestFromHKDFAlgorithm(algorithm);
    var hmac := new HMac(digest);
    var hashLength := GetHashLength(digest);

    var nonEmptySalt: seq<uint8>;
    match salt {
      case None =>
        nonEmptySalt := Fill(0, hashLength);
      case Some(s) =>
        nonEmptySalt := s;
    }

    var prk := Extract(hmac, nonEmptySalt, ikm, digest);
    okm := Expand(hmac, prk, info, L, digest, nonEmptySalt);
  }
}
