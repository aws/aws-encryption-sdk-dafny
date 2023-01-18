// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesRSA {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt

  method {:test} RSAEncryptTests() {
    var client :- expect Primitives.AtomicPrimitives();
    var keys := client.GenerateRSAKeyPair(input := Primitives.Types.GenerateRSAKeyPairInput(strength := 2048 as Primitives.Types.RSAStrengthBits));
    expect keys.Success?;

    BasicRSAEncryptTest(
      Primitives.Types.RSAEncryptInput(
        padding := Primitives.Types.RSAPaddingMode.OAEP_SHA256,
        publicKey := keys.value.publicKey.pem,
        // The string "asdf" as bytes
        plaintext := [ 97, 115, 100, 102 ]
      ),
      keys.value
    );
  }

  method BasicRSADecryptTests(
    input: Primitives.Types.RSADecryptInput,
    expectedOutput: seq<uint8>
  ) 
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSADecrypt(input);

    expect output == expectedOutput;

  }
  
  method BasicRSAEncryptTest(
    input: Primitives.Types.RSAEncryptInput,
    keypair: Primitives.Types.GenerateRSAKeyPairOutput
  ) 
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSAEncrypt(input);

    var decryptInput := Primitives.Types.RSADecryptInput(
      padding := input.padding,
      privateKey := keypair.privateKey.pem,
      cipherText := output
    );

    BasicRSADecryptTests(decryptInput, input.plaintext);
  }
}