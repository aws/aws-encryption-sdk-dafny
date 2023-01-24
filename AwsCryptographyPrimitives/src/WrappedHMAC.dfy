// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"
include "HKDF/HMAC.dfy"

module {:options "-functionSyntax:4"} WrappedHMAC {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC

  function Digest(input: Types.HMacInput)
    :( output: Result<seq<uint8>, Types.Error> )
  {

    :- Need(0 < |input.key|,
      Types.AwsCryptographicPrimitivesError(message := "Key MUST NOT be 0 bytes."));
    :- Need(|input.message| < INT32_MAX_LIMIT,
      Types.AwsCryptographicPrimitivesError(message := "Message over INT32_MAX_LIMIT"));

    var value :- HMAC.Digest(input);

    Success(value)
  }
}
