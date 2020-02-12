/* HKDF.dfy
* Rustan Leino, 28 Dec 2017.
* Matthias Schlaipfer, 11 June 2019
* This is a transcription of David Cok's HmacSha256Kdf.java into Dafny.
* There are three major parts:
*   0. Basic library stuff
*      Routine definitions and specifications. (Feel free to skip reading this part.)
*   1. Crypto library stuff
*      Formalizes the Extract-and-Expand HKDF specifications and models the Mac class
*      in the Java library.
*   2. The code to be verified
*      The hkdf routine and its correctness proof.
*
* "nfv" stands for necessary for verification
*/

include "HMAC.dfy"
include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

/**
  * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
  */
module HKDF {
  import opened HMAC
  import opened Digests
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method extract(algorithm: KeyDerivationAlgorithm, hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>) returns (prk: seq<uint8>)
    requires hmac.algorithm == algorithm && |salt| != 0
    requires algorithm != IDENTITY
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures |prk| > 0 && HashLength(algorithm) as int <= |prk|
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.init(params);
    assert hmac.InputSoFar + ikm == ikm;
    hmac.updateAll(ikm);
    prk := hmac.getResult(hmac.getMacSize());
    return prk;
  }

  method expand(algorithm: KeyDerivationAlgorithm, hmac: HMac, prk: seq<uint8>, info: seq<uint8>, n: int) returns (a: seq<uint8>)
    requires hmac.algorithm == algorithm && 1 <= n <= 255
    requires algorithm != IDENTITY
    requires 0 != |prk| && HashLength(algorithm) as int <= |prk|
    requires |info| < INT32_MAX_LIMIT
    modifies hmac
    ensures |a| == n * hmac.getMacSize() as int;
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.init(params);
    ghost var gKey := hmac.initialized.get;

    ghost var s: seq<uint8> := [];

    a := seq(n * hmac.getMacSize() as int, _ => 0);

    hmac.updateAll(info);
    hmac.updateSingle(1 as uint8);
    var TiSeq := hmac.getResult(hmac.getMacSize());
    a := TiSeq + a[|TiSeq|..];
    s := s + TiSeq;

    var i := 1;

    assert hmac.getMacSize() as int + (n-1) * |TiSeq| == |a|;
    while i < n
      invariant 1 <= i <= n
      invariant |TiSeq| == hmac.getMacSize() as int
      invariant hmac.getMacSize() as int <= |prk|
      invariant |a| == n * hmac.getMacSize() as int;
      invariant s == a[..(i * hmac.getMacSize() as int)]
      invariant hmac.initialized.Some? && hmac.initialized.get == gKey
      invariant hmac.InputSoFar == []
    {
      hmac.updateAll(TiSeq);
      hmac.updateAll(info);
      hmac.updateSingle((i+1) as uint8);
      assert (i+1) <= 255;
      assert hmac.InputSoFar == TiSeq + info + [((i+1) as uint8)];
      TiSeq := hmac.getResult(hmac.getMacSize());
      var offset := i * hmac.getMacSize() as int;
      assert offset < n * hmac.getMacSize() as int;
      assert offset < |a|;
      a := a[..offset] + TiSeq + a[(|TiSeq| + offset)..];
      s := s + TiSeq;
      i := i + 1;
    }
  }

  /**
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   **/
  method hkdf(algorithm: KeyDerivationAlgorithm, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int) returns (okm: seq<uint8>)
    requires algorithm != IDENTITY
    requires 0 <= L <= 255 * HashLength(algorithm) as int
    requires salt.None? || |salt.get| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
  {
    if L == 0 {
      return [];
    }
    var hmac := new HMac(algorithm);

    var saltNonEmpty: seq<uint8>;
    match salt {
      case None =>
        saltNonEmpty := seq(hmac.getMacSize() as int, _ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty == if salt.None? then Fill(0, hmac.getMacSize() as int) else salt.get; // nfv

    var n := 1 + (L-1) / hmac.getMacSize() as int;  // note, since L and HMAC_SIZE are strictly positive, this gives the same result in Java as in Dafny
    assert n * hmac.getMacSize() as int >= L;
    var prk := extract(algorithm, hmac, saltNonEmpty, ikm);
    okm := expand(algorithm, hmac, prk, info, n);

    // if necessary, trim padding
    if |okm| > L {
      okm := okm[..L];
    }
  }
}
