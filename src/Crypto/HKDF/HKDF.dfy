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

include "../../Util/Arrays.dfy"
include "CryptoMac.dfy"
include "../Digests.dfy"
include "HKDFSpec.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

/**
  * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
  */
module HKDF {
  import Arrays
  import opened BouncyCastleCryptoMac
  import opened Digests
  import opened HKDFSpec
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method extract(which_sha: HMAC_ALGORITHM, hmac: HMac, salt: array<uint8>, ikm: array<uint8>) returns (prk: array<uint8>)
    requires hmac.algorithm == which_sha && salt.Length != 0
    modifies hmac
    ensures prk[..] == Hash(which_sha, salt[..], ikm[..])
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.init(params);
    assert hmac.InputSoFar + ikm[..] == ikm[..]; // nfv
    hmac.updateAll(ikm);
    prk := new uint8[hmac.getMacSize()];
    var _ := hmac.doFinal(prk, 0);
    return prk;
  }

  method expand(which_sha: HMAC_ALGORITHM, hmac: HMac, prk: array<uint8>, info: array<uint8>, n: int) returns (a: array<uint8>)
    requires hmac.algorithm == which_sha && 1 <= n <= 255
    requires 0 != prk.Length && HashLength(which_sha) <= prk.Length
    modifies hmac
    ensures fresh(a)
    ensures a[..] == T(which_sha, prk[..], info[..], n)
    ensures a.Length == n * hmac.getMacSize();
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.init(params);
    ghost var gKey := hmac.initialized.get;

    ghost var s: seq<uint8> := [];  // s == T(0)
    a := new uint8[n * hmac.getMacSize()];
    var TiArr: array<uint8> := new uint8[hmac.getMacSize()];

    // T(1)
    hmac.updateAll(info);
    hmac.updateSingle(1 as uint8);
    var _ := hmac.doFinal(TiArr, 0);
    Arrays.Array.copyTo(TiArr, a, 0);
    s := s + TiArr[..];

    var i := 1;

    // The following invariant simplifies the proof obligation needed to establish the precondition of Arrays.Array.copyTo
    // Before adding it, z3's outcome was unstable
    // TODO: Identify a way to make this less brittle (https://github.com/awslabs/aws-encryption-sdk-dafny/issues/99)
    assert hmac.getMacSize() + (n-1)*TiArr.Length == a.Length;
    while i < n
      invariant 1 <= i <= n
      invariant TiArr.Length == HashLength(which_sha)
      invariant TiArr[..] == Ti(which_sha, prk[..], info[..], i)[..]
      invariant HashLength(which_sha) <= prk.Length
      invariant s == T(which_sha, prk[..], info[..], i)     // s == T(1) | ... | T(i)
      invariant s == a[..i * hmac.getMacSize()]
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
      Arrays.Array.copyTo(TiArr, a, i*hmac.getMacSize());
      s := s + TiArr[..]; // s == T(1) | ... | T(i) | T(i+1)
      i := i + 1;
    }
  }

  /**
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   **/
  method hkdf(which_sha: HMAC_ALGORITHM, salt: Option<array<uint8>>, ikm: array<uint8>, info: array<uint8>, L: int) returns (okm: array<uint8>)
    requires which_sha == HmacSHA256 || which_sha == HmacSHA384
    requires 0 <= L <= 255 * HashLength(which_sha)
    requires salt.None? || salt.get.Length != 0
    ensures fresh(okm)
    ensures okm.Length == L
    ensures
      // Extract:
      var prk := Hash(which_sha, if salt.None? then Fill(0, HashLength(which_sha)) else salt.get[..], ikm[..]);
      // Expand:
      okm[..L] == TMaxLength(which_sha, prk, info[..])[..L]
  {
    if L == 0 {
      return new uint8[0];
    }
    var hmac := new HMac(which_sha);

    var saltNonEmpty: array<uint8>;
    match salt {
      case None =>
        saltNonEmpty := new uint8[hmac.getMacSize()](_ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty[..] == if salt.None? then Fill(0, hmac.getMacSize()) else salt.get[..]; // nfv

    var n := 1 + (L-1) / hmac.getMacSize();  // note, since L and HMAC_SIZE are strictly positive, this gives the same result in Java as in Dafny
    assert n * hmac.getMacSize() >= L;
    var prk := extract(which_sha, hmac, saltNonEmpty, ikm);

    okm := expand(which_sha, hmac, prk, info, n);

    // if necessary, trim padding
    if okm.Length > L {
      okm := Arrays.Array.copy(okm, L);
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
