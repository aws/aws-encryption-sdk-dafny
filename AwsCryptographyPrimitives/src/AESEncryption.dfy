// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  // The following are used to tie plaintext and ciphertext with the AAD that was used to produce them.
  // These assumptions can be used in the postconditions of externs, and be referenced elsewhere
  // in order to ensure that the AAD used is as expected.
  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
  predicate {:axiom} EncryptionOutputEncryptedWithAAD(output: Types.AESEncryptOutput, aad: seq<uint8>)
  predicate {:axiom} CiphertextGeneratedWithPlaintext (ciphertext: seq<uint8>, plaintext: seq<uint8>)
  predicate {:axiom} EncryptedWithKey(ciphertext: seq<uint8>, key: seq<uint8>)
  predicate {:axiom} DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: Types.AES_GCM): (encArt: Types.AESEncryptOutput)
    requires 0 < encAlg.tagLength 
    requires encAlg.tagLength as nat <= |s|
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLength as int
  {
    assert |s| - encAlg.tagLength as int <= |s|;

    var cipherText := s[.. |s| - encAlg.tagLength as int];
    var authTag := s[|s| - encAlg.tagLength as int ..];

    Types.AESEncryptOutput(cipherText := cipherText, authTag := authTag)
  }

  method {:extern "AESEncryption.AES_GCM", "AESEncryptExtern"} AESEncryptExtern(
    encAlg: Types.AES_GCM,
    iv: seq<uint8>,
    key: seq<uint8>,
    msg: seq<uint8>,
    aad: seq<uint8>
  )
    returns (res : Result<Types.AESEncryptOutput, Types.OpaqueError>)
    requires |iv| == encAlg.ivLength as int
    requires |key| == encAlg.keyLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)

  method AESEncrypt(input: Types.AESEncryptInput)
    returns (res : Result<Types.AESEncryptOutput, Types.Error>)
    ensures res.Success? ==>
      && |res.value.cipherText| == |input.msg|
      && |res.value.authTag| == input.encAlg.tagLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, input.msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, input.key)
    // This is useful information to have to prove correctness
    ensures res.Success? ==> |res.value.authTag| == input.encAlg.tagLength as nat
  {

    :- Need(
      && |input.iv| == input.encAlg.ivLength as int
      && |input.key| == input.encAlg.keyLength as int,
      Types.AwsCryptographicPrimitivesError(message := "Request does not match algorithm.")
    );

    var AESEncryptInput(encAlg, iv, key, msg, aad) := input;

    var value :- AESEncryptExtern(encAlg, iv, key, msg, aad);

    :- Need(
      |value.cipherText| == |msg|,
      Types.AwsCryptographicPrimitivesError(message := "AESEncrypt did not return cipherText of expected length")
    );
    :- Need(
      |value.authTag| == encAlg.tagLength as int,
      Types.AwsCryptographicPrimitivesError(message := "AESEncryption did not return valid tag")
    );

    return Success(value);
}

  method {:extern "AESEncryption.AES_GCM", "AESDecryptExtern"} AESDecryptExtern(
    encAlg: Types.AES_GCM,
    key: seq<uint8>,
    cipherTxt: seq<uint8>,
    authTag: seq<uint8>,
    iv: seq<uint8>,
    aad: seq<uint8>
  )
    returns (res: Result<seq<uint8>, Types.OpaqueError>)
    requires |key| == encAlg.keyLength as int
    requires |iv| == encAlg.ivLength as int
    requires |authTag| == encAlg.tagLength as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)

  method AESDecrypt(
    input: Types.AESDecryptInput
  )
    returns (res: Result<seq<uint8>, Types.Error>)
    ensures res.Success? ==> |res.value| == |input.cipherTxt|
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(input.cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(input.key, res.value)
  {
    :- Need(
      && |input.key| == input.encAlg.keyLength as int
      && |input.iv| == input.encAlg.ivLength as int
      && |input.authTag| == input.encAlg.tagLength as int,
      Types.AwsCryptographicPrimitivesError(message := "Request does not match algorithm.")
    );

    var AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad) := input;
    var value :- AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);

    :- Need(
      |cipherTxt| == |value|,
      Types.AwsCryptographicPrimitivesError(message := "AESDecrypt did not return plaintext of expected length")
    );

    return Success(value);
  }

}
