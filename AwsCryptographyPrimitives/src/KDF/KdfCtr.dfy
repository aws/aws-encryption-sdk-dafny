// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../HKDF/HMAC.dfy"
include "../Digest.dfy"
include "../../Model/AwsCryptographyPrimitivesTypes.dfy"

/*
 * Implementation of the https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-108r1.pdf
 * Key Derivation in Counter Mode Using Pseudorandom Functions
 */
module KdfCtr {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC
  import Digest

  const SEPARATION_INDICATOR: seq<uint8> := [0x00];
  const COUNTER_START_VALUE: uint32 := 1;

  // This implementation of te spec is restricted to only deriving
  // 32 bytes of key material. We will have to consider the effect of allowing different
  // key length to the hierarchy keyring.
  method KdfCounterMode(input: Types.KdfCtrInput)
    returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
  {
    :- Need(
      // Although KDF can support multiple digests; for our use case we only want
      // to use SHA 256; we may rethink this if we ever want to support other algorithms
      // We are requiring the requested length to be 32 bytes since this is only used for the hierarchy
      // keyring it requires to derive a 32 byte key.
      && input.digestAlgorithm == Types.DigestAlgorithm.SHA_256
      && |input.ikm| == 32
      && input.nonce.Some?
      && |input.nonce.value| == 16 
      && input.expectedLength == 32
      && 0 < ((input.expectedLength as int) * 8) as int < INT32_MAX_LIMIT,
      Types.AwsCryptographicPrimitivesError(message := "Kdf in Counter Mode input is invalid.")
    );
    
    var ikm := input.ikm;
    var label_ := input.purpose.UnwrapOr([]);
    var info := input.nonce.UnwrapOr([]);
    var okm := [];

    // Compute length in bits of the input going into the PRF.
    var internalLength : uint32 := (4 + |SEPARATION_INDICATOR| + 4) as uint32;
    :- Need(
      && internalLength as int + |label_| + |info| < INT32_MAX_LIMIT, 
      Types.AwsCryptographicPrimitivesError(message:= "Input Length exceeds INT32_MAX_LIMIT")
    );

    // Compute length in bits of the output from the PRF. "L" in SP800-108.
    var lengthBits : seq<uint8> := UInt.UInt32ToSeq((input.expectedLength * 8) as uint32);
    var explicitInfo := label_ + SEPARATION_INDICATOR + info + lengthBits;

    :- Need(
      4 + |explicitInfo| < INT32_MAX_LIMIT,
      Types.AwsCryptographicPrimitivesError(message := "PRF input length exceeds INT32_MAX_LIMIT.")
    );

    okm :- RawDerive(ikm, explicitInfo, input.expectedLength, 0);

    return Success(okm);
  }

  method RawDerive(ikm: seq<uint8>, explicitInfo: seq<uint8>, length: int32, offset: int32)
    returns (output: Result<seq<uint8>, Types.Error>)
    requires 
      && |ikm| == 32
      && length == 32
      && 4 + |explicitInfo| < INT32_MAX_LIMIT
      && length as int + Digest.Length(Types.DigestAlgorithm.SHA_256) < INT32_MAX_LIMIT - 1
    ensures output.Success? ==> |output.value| == length as int
  {
    // We will only support HMAC_SHA256, so no need to support additional Digests
    var derivationMac := Types.DigestAlgorithm.SHA_256;
    var hmac :- HMAC.HMac.Build(derivationMac);
    hmac.Init(key := ikm);

    var macLengthBytes := Digest.Length(derivationMac) as int32; // "h" in SP800-108
    // Number of iterations required to compose output of required length.
    var iterations := (length + macLengthBytes - 1) / macLengthBytes; // "n" in SP800-108
    var buffer := [];

    // Counter "i"
    var i : seq<uint8> := UInt.UInt32ToSeq(COUNTER_START_VALUE);

    for iteration := 1 to iterations + 1
      invariant |i| == 4
      invariant hmac.GetKey() == ikm
    {
      /*
       * SP800-108 defines PRF(s,x), the "x" variable is prfInput below.
       */
      // i || label || 0x00 || context (info) || L
      hmac.Update(i);
      hmac.Update(explicitInfo);
      var tmp := hmac.GetResult();
      buffer := buffer + tmp;

      i :- Increment(i);
    }

    :- Need(
      |buffer| >= length as int,
      Types.AwsCryptographicPrimitivesError(message := "Failed to derive key of requested length")
    );

    return Success(buffer[..length]);
  }
  
  function method Increment(x : seq<uint8>) : (ret : Result<seq<uint8>, Types.Error>)
    requires |x| == 4
    ensures ret.Success? ==> |ret.value| == 4
  {
    // increments the counter x which represents the number of iterations
    // as a bit sequence
    if x[3] < 255 then
      Success([x[0], x[1], x[2], x[3]+1])
    else if x[2] < 255 then
      Success([x[0], x[1], x[2]+1, 0])
    else if x[1] < 255 then
      Success([x[0], x[1]+1, 0, 0])
    else if x[0] < 255 then
      Success([x[0]+1, 0, 0, 0])
    else
      Failure(Types.AwsCryptographicPrimitivesError(message := "Unable to derive key material; may have exceeded limit."))
  }

}
