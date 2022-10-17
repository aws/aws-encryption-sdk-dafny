// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesAES {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import Digest

  method {:test} AESDecryptTests() {


    // How to create test vector in Node.js
    // p = Buffer.from([ 97, 115, 100, 102 ])

    // key = Buffer.from(Array(32).fill(1))
    // iv = Buffer.from(Array(12).fill(2))
    // aad = Buffer.from([3,3,3,3])

    // c = crypto.createCipheriv('aes-256-gcm', key, iv)
    // c.setAAD(aad)
    // o = c.update(p)
    // f = c.final()
    // t = c.getAuthTag()

    // d = crypto.createDecipheriv('aes-256-gcm', key, iv)
    // d.setAAD(aad)
    // d.setAuthTag(t)
    // out = d.update(o)
    // d.final()

    BasicAESDecryptTest(
      Primitives.Types.AESDecryptInput(
        encAlg := Primitives.Types.AES_GCM(
          keyLength := 32 as int32,
          tagLength := 16 as int32,
          ivLength := 12 as int32
        ),
        key := [
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1
        ],
        cipherTxt := [ 102, 165, 173, 47 ],
        authTag := [
          54, 200,  18,  56, 172,
          194, 174,  23, 239, 151,
          47, 180, 143, 232, 142,
          184
        ],
        iv := [
          2, 2, 2, 2, 2,
          2, 2, 2, 2, 2,
          2, 2
        ],
        aad := [3,3,3,3]
      ),
      // The string "asdf" as bytes
      [ 97, 115, 100, 102 ]
    );

  }

  method {:test} AESEncryptTests() {
    BasicAESEncryptTest(
      Primitives.Types.AESEncryptInput(
        encAlg := Primitives.Types.AES_GCM(
          keyLength := 32 as int32,
          tagLength := 16 as int32,
          ivLength := 12 as int32
        ),
        iv := [
          2, 2, 2, 2, 2,
          2, 2, 2, 2, 2,
          2, 2
        ],
        key := [
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1
        ],
        // The string "asdf" as bytes
        msg := [ 97, 115, 100, 102 ],
        aad := [3,3,3,3]
      )
    );
  }

  method BasicAESDecryptTest(
    input: Primitives.Types.AESDecryptInput,
    expectedOutput: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.AESDecrypt(input);
    expect output == expectedOutput;
  }

  method BasicAESEncryptTest(
    input: Primitives.Types.AESEncryptInput
  )
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.AESEncrypt(input);

    var decryptInput := Primitives.Types.AESDecryptInput(
      encAlg := input.encAlg,
      key := input.key,
      cipherTxt := output.cipherText,
      authTag := output.authTag,
      iv := input.iv,
      aad := input.aad
    );

    BasicAESDecryptTest(decryptInput, input.msg);
  }
}
