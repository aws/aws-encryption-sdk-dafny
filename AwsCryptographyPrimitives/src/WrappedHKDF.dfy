// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "HKDF/HKDF.dfy"
include "HKDF/HMAC.dfy"
include "Digest.dfy"
include "../Model/AwsCryptographyPrimitivesTypes.dfy"

/*
 * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
 */
module WrappedHKDF {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import StandardLibrary
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC
  import HKDF
  import Digest

  method Extract(input: Types.HkdfExtractInput)
    returns (output: Result<seq<uint8>, Types.Error>)
  {

    :- Need(
      && (input.salt.None? || |input.salt.value| != 0)
      && |input.ikm| < INT32_MAX_LIMIT,
      Types.AwsCryptographicPrimitivesError(message := "HKDF Extract needs a salt and reasonable ikm.")
    );

    var HkdfExtractInput(digestAlgorithm, salt, ikm) := input;

    var hmac :- HMAC.HMac.Build(digestAlgorithm);
    var prk := HKDF.Extract(
      hmac,
      salt.UnwrapOr(StandardLibrary.Fill(0, Digest.Length(digestAlgorithm))),
      ikm,
      digestAlgorithm
    );

    return Success(prk);
  }

  method Expand(input: Types.HkdfExpandInput)
    returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
  {

    :- Need(
      && 1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
      && |input.info| < INT32_MAX_LIMIT
      && Digest.Length(input.digestAlgorithm) == |input.prk|,
      Types.AwsCryptographicPrimitivesError(message := "HKDF Expand needs valid input.")
    );
    var HkdfExpandInput(digestAlgorithm, prk, info, expectedLength) := input;

    var hmac :- HMAC.HMac.Build(digestAlgorithm);
    var omk, _ := HKDF.Expand(
      hmac,
      prk,
      info,
      expectedLength as int,
      digestAlgorithm
    );

    return Success(omk);
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(input: Types.HkdfInput)
    returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
  {

    :- Need(
      && 1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
      && (input.salt.None? || |input.salt.value| != 0)
      && |input.info| < INT32_MAX_LIMIT
      && |input.ikm| < INT32_MAX_LIMIT,
      Types.AwsCryptographicPrimitivesError(message := "Wrapped Hkdf input is invalid.")
    );
    var HkdfInput(digest, salt, ikm, info, expectedLength) := input;

    var okm := HKDF.Hkdf(
      digest,
      salt,
      ikm,
      info,
      expectedLength as int
    );

    return Success(okm);
  }
}
