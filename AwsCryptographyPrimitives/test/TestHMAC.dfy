// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestAwsCryptographyPrimitivesHMacDigest {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import Digest
  import opened Wrappers

  method {:test} DigestTests() {
    var client :- expect Primitives.AtomicPrimitives();

    HmacSHA_256(client);
    HmacSHA_384(client);
    HmacSHA_512(client);
  }

  method HmacSHA_256(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var _ :- expect BasicHMacTest(
      client := client,
      input := Types.HMacInput(
        digestAlgorithm := Types.SHA_256,
        key := [1,1,1,1],
        // The string "asdf" as bytes
        message := [ 97, 115, 100, 102 ]
      ),
      expectedDigest := [
        93,  12,  86, 145, 123, 239, 169,  72,
        195, 226, 204, 179, 103,  94, 195,  83,
        134, 128, 226, 185, 184, 203,  98, 100,
        115,  32,   7,  44, 172,  11,  81,  16
      ]
    );
  }
  method HmacSHA_384(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var _ :- expect BasicHMacTest(
      client := client,
      input := Types.HMacInput(
        digestAlgorithm := Types.SHA_384,
        key := [1,1,1,1],
        // The string "asdf" as bytes
        message := [ 97, 115, 100, 102 ]
      ),
      expectedDigest := [
        219,  44,  51,  60, 217,  57, 186, 208,   8,  69,
        115, 185, 190, 136, 136,   1,  69, 143, 151, 148,
          7,  66, 149, 193,  16, 225,  51,  85,  92, 176,
        139, 249,  56,  93, 189,  11, 150,  21, 135,  54,
        153,  37,  76,  68,  70,  77, 154, 124
      ]
    );
  }
  method HmacSHA_512(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var _ :- expect BasicHMacTest(
      client := client,
      input := Types.HMacInput(
        digestAlgorithm := Types.SHA_512,
        key := [1,1,1,1],
        // The string "asdf" as bytes
        message := [ 97, 115, 100, 102 ]
      ),
      expectedDigest := [
        49, 213,  21, 219,  23, 169, 195,  39, 177,  1,  15,
        162, 233, 182, 208,  84, 226,   3,  27, 120, 75,  78,
        85,  46, 220,   5, 166, 206,  79,  47,  25, 94,  88,
        119, 211, 192, 148,  23, 252, 155,  98, 218, 97, 225,
        38,  93,  83, 113, 139,  95, 101, 222, 154, 98, 244,
        206,  88, 229,   6, 115, 226, 188, 152, 173
      ]
    );
  }

  function method BasicHMacTest(
    nameonly client: Types.IAwsCryptographicPrimitivesClient,
    nameonly input: Types.HMacInput,
    nameonly expectedDigest: seq<uint8>
  ) : Result<(), Types.Error>
    requires client.ValidState()
    ensures client.ValidState()
  {

    var output :- client.HMac(input);

    :- Need(|output| == Digest.Length(input.digestAlgorithm), Types.AwsCryptographicPrimitivesError( message := "Error"));
    :- Need(output == expectedDigest, Types.AwsCryptographicPrimitivesError( message := "Error"));

    Success(())
  }
}
