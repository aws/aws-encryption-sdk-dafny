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

  method Extract(algorithm: KeyDerivationAlgorithm, hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>) returns (prk: seq<uint8>)
    requires hmac.algorithm == algorithm && |salt| != 0
    requires algorithm != IDENTITY
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures |prk| > 0 && GetHashLength(algorithm) as int == |prk|
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.Init(params);
    hmac.Update(ikm, 0, |ikm| as int32);
    prk := hmac.GetResult();
    return prk;
  }

  method Expand(algorithm: KeyDerivationAlgorithm, hmac: HMac, prk: seq<uint8>, info: seq<uint8>, n: int) returns (a: seq<uint8>)
    requires hmac.algorithm == algorithm && 1 <= n <= 255
    requires algorithm != IDENTITY
    requires 0 != |prk| && GetHashLength(algorithm) as int == |prk|
    requires |info| < INT32_MAX_LIMIT
    modifies hmac
    ensures |a| == n * GetHashLength(algorithm) as int;
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.Init(params);
    ghost var hashLength := GetHashLength(algorithm);

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
  method Hkdf(algorithm: KeyDerivationAlgorithm, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int) returns (okm: seq<uint8>)
    requires algorithm != IDENTITY
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

    var n := 1 + (L-1) / hashLength as int;
    assert n * hashLength as int >= L;
    var prk := Extract(algorithm, hmac, saltNonEmpty, ikm);
    okm := Expand(algorithm, hmac, prk, info, n);

    // if necessary, trim padding
    if |okm| > L {
      okm := okm[..L];
    }
  }
}
