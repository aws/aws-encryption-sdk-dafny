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
include "HKDFSpec.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

/**
  * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
  */
module HKDF {
  import opened HMAC
  import opened Digests
  import opened HKDFSpec
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method extract(which_sha: KeyDerivationAlgorithm, hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>) returns (prk: seq<uint8>)
    requires hmac.algorithm == which_sha && |salt| != 0
    requires which_sha != IDENTITY
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures prk[..] == Hash(which_sha, salt[..], ikm[..])
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.init(params);
    assert hmac.InputSoFar + ikm[..] == ikm[..]; // nfv
    hmac.updateAll(ikm);
    prk := seq(hmac.getMacSize() as int, i => 0);
    var _ := hmac.doFinal(prk, 0);
    return prk;
  }

  method expand(which_sha: KeyDerivationAlgorithm, hmac: HMac, prk: seq<uint8>, info: seq<uint8>, n: int) returns (a: seq<uint8>)
    requires hmac.algorithm == which_sha && 1 <= n <= 255
    requires which_sha != IDENTITY
    requires 0 != |prk| && HashLength(which_sha) as int <= |prk|
    requires |info| < INT32_MAX_LIMIT
    modifies hmac
    ensures a[..] == T(which_sha, prk[..], info[..], n)
    ensures |a| == n * hmac.getMacSize() as int;
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.init(params);
    ghost var gKey := hmac.initialized.get;

    ghost var s: seq<uint8> := [];  // s == T(0)

    a := seq(n * hmac.getMacSize() as int, i => 0);
    var TiArr: seq<uint8> := seq(hmac.getMacSize() as int, i => 0);

    // T(1)
    hmac.updateAll(info);
    hmac.updateSingle(1 as uint8);
    var _ := hmac.doFinal(TiArr, 0);
    a := a[..0] + TiArr[..] + a[|TiArr|..];
    s := s + TiArr[..];

    var i := 1;

    assert hmac.getMacSize() as int + (n-1) * |TiArr| == |a|;
    while i < n
      invariant 1 <= i <= n
      invariant |TiArr| == HashLength(which_sha) as int
      invariant TiArr[..] == Ti(which_sha, prk[..], info[..], i)[..]
      invariant HashLength(which_sha) as int <= |prk|
      invariant s == T(which_sha, prk[..], info[..], i)     // s == T(1) | ... | T(i)
      invariant |a| == n * hmac.getMacSize() as int;
      invariant s == a[..i * hmac.getMacSize() as int]
      invariant hmac.initialized.Some? && hmac.initialized.get == gKey
      invariant hmac.InputSoFar == []
    {
      // T(i+1)
      hmac.updateAll(TiArr);
      hmac.updateAll(info);
      hmac.updateSingle((i+1) as uint8);
      assert (i+1) <= 255;
      assert hmac.InputSoFar[..] == TiArr[..] + info[..] + [((i+1) as uint8)]; // nfv
      var _ := hmac.doFinal(TiArr, 0);
      var offset := i * hmac.getMacSize() as int;
      assert offset <  n * hmac.getMacSize() as int;
      assert offset < |a|;
      a := a[..offset] + TiArr[..] + a[(|TiArr| + offset)..];
      s := s + TiArr[..]; // s == T(1) | ... | T(i) | T(i+1)
      i := i + 1;
    }
  }

  /**
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   **/
  method hkdf(which_sha: KeyDerivationAlgorithm, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int) returns (okm: seq<uint8>)
    requires which_sha != IDENTITY
    requires 0 <= L <= 255 * HashLength(which_sha) as int
    requires salt.None? || |salt.get| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
    ensures
      // Extract:
      var prk := Hash(which_sha, if salt.None? then Fill(0, HashLength(which_sha) as int) else salt.get[..], ikm[..]);
      // Expand:
      okm[..L] == TMaxLength(which_sha, prk, info[..])[..L]
  {
    if L == 0 {
      return [];
    }
    var hmac := new HMac(which_sha);

    var saltNonEmpty: seq<uint8>;
    match salt {
      case None =>
        saltNonEmpty := seq(hmac.getMacSize(), _ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty[..] == if salt.None? then Fill(0, hmac.getMacSize() as int) else salt.get[..]; // nfv

    var n := 1 + (L-1) / hmac.getMacSize() as int;  // note, since L and HMAC_SIZE are strictly positive, this gives the same result in Java as in Dafny
    assert n * hmac.getMacSize() as int >= L;
    var prk := extract(which_sha, hmac, saltNonEmpty, ikm);

    okm := expand(which_sha, hmac, prk, info, n);

    // if necessary, trim padding
    if |okm| > L {
      okm := okm[..L];
    }
    calc {
      okm[..L];
    ==
      T(which_sha, prk[..], info[..], n)[..L];
    ==  { TPrefix(which_sha, prk[..], info[..], n, 255); }
      TMaxLength(which_sha, prk[..], info[..])[..L];
    }
  }
}
