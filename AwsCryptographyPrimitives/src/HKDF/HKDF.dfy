// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "HMAC.dfy"
include "../Digest.dfy"
include "../../Model/AwsCryptographyPrimitivesTypes.dfy"

/*
 * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
 */
module HKDF {
  import opened HMAC
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import Digest


  // 2.2.  Step 1: Extract
  // 
  //  HKDF-Extract(salt, IKM) -> PRK
  // 
  //  Options:
  //     Hash     a hash function; HashLen denotes the length of the
  //              hash function output in octets
  // 
  //  Inputs:
  //     salt     optional salt value (a non-secret random value);
  //              if not provided, it is set to a string of HashLen zeros.
  //     IKM      input keying material
  // 
  //  Output:
  //     PRK      a pseudorandom key (of HashLen octets)
  // 
  //  The output PRK is calculated as follows:
  // 
  //  PRK = HMAC-Hash(salt, IKM)
  method Extract(
    hmac: HMac,
    salt: seq<uint8>,
    ikm: seq<uint8>, 
    ghost digest: Types.DigestAlgorithm
  )
    returns (prk: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures Digest.Length(hmac.GetDigest()) == |prk|
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

  // T is relational since the external hashMethod hmac.GetKey() ensures that the input and output of the hash method are in the relation hmac.HashSignature
  // T depends on Ti and Ti depends on hmac.HashSignature
  // T and Ti come from https://www.rfc-editor.org/rfc/rfc5869#section-2.3
  //    The output OKM is calculated as follows:
  // 
  //  N = ceil(L/HashLen)
  //  T = T(1) | T(2) | T(3) | ... | T(N)
  //  OKM = first L octets of T

  //  where:
  //  T(0) = empty string (zero length)
  //  T(1) = HMAC-Hash(PRK, T(0) | info | 0x01)
  //  T(2) = HMAC-Hash(PRK, T(1) | info | 0x02)
  //  T(3) = HMAC-Hash(PRK, T(2) | info | 0x03)
  //  ...

  //  (where the constant concatenated to the end of each T(n) is a
  //  single octet.)
  predicate T(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then
      [] == res
    else
      var nMinusOne := n - 1;
      exists prev1, prev2 :: T(hmac, info, nMinusOne, prev1) && Ti(hmac, info, n, prev2) && prev1 + prev2 == res
  }

  predicate Ti(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n, 1
  {
    if n == 0 then
      res == []
    else
      exists prev :: PreTi(hmac, info, n, prev) &&  hmac.HashSignature(prev, res)
  }

    // return T (i)
  predicate PreTi(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 1 <= n < 256
    decreases n, 0
  {
    var nMinusOne := n - 1;
    exists prev | Ti(hmac, info, nMinusOne, prev) :: res == prev + info + [(n as uint8)]
  }

  // 2.3.  Step 2: Expand
  // 
  //    HKDF-Expand(PRK, info, L) -> OKM
  // 
  //    Options:
  //       Hash     a hash function; HashLen denotes the length of the
  //                hash function output in octets
  // 
  //    Inputs:
  //       PRK      a pseudorandom key of at least HashLen octets
  //                (usually, the output from the extract step)
  //       info     optional context and application specific information
  //                (can be a zero-length string)
  //       L        length of output keying material in octets
  //                (<= 255*HashLen)
  // 
  //    Output:
  //       OKM      output keying material (of L octets)
  method Expand(
    hmac: HMac, 
    prk: seq<uint8>, 
    info: seq<uint8>, 
    expectedLength: int, 
    digest: Types.DigestAlgorithm
  ) returns (
      okm: seq<uint8>, 
      ghost okmUnabridged: seq<uint8>
  )
    requires hmac.GetDigest() == digest
    requires 1 <= expectedLength <= 255 * Digest.Length(hmac.GetDigest())
    requires |info| < INT32_MAX_LIMIT
    requires Digest.Length(hmac.GetDigest()) == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.GetKey() == prk
    ensures hmac.GetDigest() == digest
    ensures var n := (Digest.Length(digest) + expectedLength - 1) / Digest.Length(digest);
      && T(hmac, info, n, okmUnabridged)
      && (|okmUnabridged| <= expectedLength ==> okm == okmUnabridged)
      && (expectedLength < |okmUnabridged| ==> okm == okmUnabridged[..expectedLength])
  {
    // N = ceil(L / Hash Length)
    var hashLength := Digest.Length(digest);
    var n := (hashLength + expectedLength - 1) / hashLength;
    assert 0 <= n < 256;

    // T(0) = empty string (zero length)
    hmac.Init(prk);
    var t_prev := [];
    var t_n := t_prev;

    // T = T(0) + T (1) + T(2) + ... T(n)
    // T(1) = HMAC-Hash(PRK, T(1) | info | 0x01)
    // ...
    // T(n) = HMAC- Hash(prk, T(n - 1) | info | 0x0n)
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |t_prev| == if i == 1 then 0 else hashLength
      invariant hashLength == |prk|
      invariant |t_n| == (i - 1) * hashLength
      invariant hmac.GetKey() == prk
      invariant hmac.GetDigest() == digest
      invariant hmac.GetInputSoFar() == []
      invariant T(hmac, info, i - 1, t_n)
      invariant Ti(hmac, info, i - 1, t_prev)
    {
      hmac.Update(t_prev);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.GetInputSoFar() == t_prev + info + [i as uint8];

      // Add additional verification for T(n): github.com/awslabs/aws-encryption-sdk-dafny/issues/177
      t_prev := hmac.GetResult();
      // t_n == T(i - 1)
      assert Ti(hmac, info, i, t_prev);

      t_n := t_n + t_prev;
      // t_n == T(i) == T(i - 1) + Ti(i)
      i := i + 1;
      assert T(hmac, info, i - 1, t_n);
    }

    // okm = first L (expectedLength) bytes of T(n)
    okm := t_n;
    okmUnabridged := okm;
    assert T(hmac, info, n, okmUnabridged);

    if expectedLength < |okm| {
      okm := okm[..expectedLength];
    }
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(
    digest: Types.DigestAlgorithm, 
    salt: Option<seq<uint8>>, 
    ikm: seq<uint8>, 
    info: seq<uint8>, 
    L: int
  ) returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * Digest.Length(digest)
    requires salt.None? || |salt.value| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
  {
    if L == 0 {
      return [];
    }
    var hmac := new HMac(digest);
    var hashLength := Digest.Length(digest);

    var nonEmptySalt: seq<uint8>;
    match salt {
      case None =>
        nonEmptySalt := StandardLibrary.Fill(0, hashLength);
      case Some(s) =>
        nonEmptySalt := s;
    }

    var prk := Extract(hmac, nonEmptySalt, ikm, digest);
    ghost var okmUnabridged;
    okm, okmUnabridged := Expand(hmac, prk, info, L, digest);
  }
}
