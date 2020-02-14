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
    ensures hmac.getKey().Some? && hmac.getKey().get == salt
    ensures hmac.getAlgorithm() == algorithm
  {
    // prk = HMAC-Hash(salt, ikm)
    var params: CipherParameters := KeyParameter(salt);
    hmac.Init(params);
    hmac.Update(ikm, 0, |ikm| as int32);
    assert hmac.getInputSoFar() == ikm;

    prk := hmac.GetResult();
    assert hmac.getInputSoFar() == [];
    return prk;
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, L: int, algorithm: HKDFAlgorithms, ghost salt: seq<uint8>) returns (okm: seq<uint8>)
    requires hmac.getAlgorithm() == algorithm
    requires 1 <= L <= 255 * GetHashLength(hmac.getAlgorithm()) as int
    requires hmac.getKey().Some? && hmac.getKey().get == salt
    requires |info| < INT32_MAX_LIMIT
    requires GetHashLength(hmac.getAlgorithm()) as int == |prk|
    modifies hmac
    ensures |okm| == L
    ensures hmac.getKey().Some? && hmac.getKey().get == prk
  {
    // N = ceil(L / Hash Length)
    var hashLength := GetHashLength(algorithm);
    var n := 1 + (L - 1) / hashLength as int;

    // T(0) = empty string (zero length)
    var params: CipherParameters := KeyParameter(prk);
    hmac.Init(params);
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
      invariant hmac.getKey().Some? && hmac.getKey().get == prk
      invariant hmac.getAlgorithm() == algorithm
      invariant hmac.getInputSoFar() == []
    {
      hmac.Update(t_last, 0, |t_last| as int32);
      hmac.Update(info, 0, |info| as int32);
      hmac.UpdateSingle(i as uint8);
      assert hmac.getInputSoFar() == t_last + info + [(i as uint8)];

      t_last := hmac.GetResult();
      assert hmac.getInputSoFar() == [];

      // Add additional verification for t: github.com/awslabs/aws-encryption-sdk-dafny/issues/177
      t_n := t_n + t_last;
      i := i + 1;
    }

    // okm = first L octets of T
    okm := t_n;
    if |okm| > L {
      okm := okm[..L];
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
    assert hmac.getAlgorithm() == algorithm;
    var hashLength := GetHashLength(algorithm);

    var saltNonEmpty: seq<uint8>;
    match salt {
      case None =>
        saltNonEmpty := seq(hashLength as int, _ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty == if salt.None? then Fill(0, hashLength as int) else salt.get;

    var prk := Extract(hmac, saltNonEmpty, ikm, algorithm);
    assert hmac.getAlgorithm() == algorithm;
    okm := Expand(hmac, prk, info, L, algorithm, saltNonEmpty);
  }
}
