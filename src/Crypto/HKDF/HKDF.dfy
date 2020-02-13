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

  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>) returns (prk: seq<uint8>)
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    ensures GetHashLength(hmac.algorithm) as int == |prk|
    ensures hmac.initialized.Some?
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.Init(params);
    hmac.Update(ikm, 0, |ikm| as int32);
    prk := hmac.GetResult();
    return prk;
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, n: int) returns (a: seq<uint8>)
    requires 1 <= n <= 255
    requires hmac.initialized.Some?
    requires |info| < INT32_MAX_LIMIT
    requires GetHashLength(hmac.algorithm) as int == |prk|
    ensures |a| == n * GetHashLength(hmac.algorithm) as int;
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.Init(params);
    ghost var hashLength := GetHashLength(hmac.algorithm);

    a := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant hashLength as int == |prk|
      invariant |a| == i * hashLength as int;
      invariant hmac.initialized.Some?
    {
      hmac.Update(info, 0, |info| as int32);
      hmac.UpdateSingle((i + 1) as uint8);
      var TiSeq := hmac.GetResult();
      a := a + TiSeq;
      i := i + 1;
      assert i <= 255;
      // Don't update if this was the final loop (since we won't update a again anyways)
      if i != n {
        hmac.Update(TiSeq, 0, |TiSeq| as int32);
      }
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
        saltNonEmpty := seq(hashLength as int, _ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty == if salt.None? then Fill(0, hashLength as int) else salt.get;

    var n := 1 + (L - 1) / hashLength as int;
    assert n * hashLength as int >= L;
    var prk := Extract(hmac, saltNonEmpty, ikm);
    okm := Expand(hmac, prk, info, n);

    // if necessary, trim padding
    if |okm| > L {
      okm := okm[..L];
    }
  }
}
