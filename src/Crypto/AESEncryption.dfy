// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"
include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, AESDecryptExtern, AESEncryptExtern, Wrappers,
      UInt, PlaintextDecryptedWithAAD, EncryptionOutputEncryptedWithAAD, CiphertextGeneratedWithPlaintext,
      EncryptedWithKey, DecryptedWithKey
    reveals 
      EncryptionOutput, 
      AES_GCM,
      KeyLength,
      TagLength,
      IVLength

  type KeyLength = l: uint8 | l == 32 || l == 24 || l == 16 witness 32
  type TagLength = l: uint8 | l == 16 witness 16
  type IVLength = l: uint8 | l == 12 witness 12

  datatype AES_GCM = AES_GCM(
    nameonly keyLength: KeyLength,
    nameonly tagLength: TagLength,
    nameonly ivLength: IVLength
  )

  datatype EncryptionOutput = EncryptionOutput(cipherText: seq<uint8>, authTag: seq<uint8>)

  // The following are used to tie plaintext and ciphertext with the AAD that was used to produce them.
  // These assumptions can be used in the postconditions of externs, and be referenced elsewhere
  // in order to ensure that the AAD used is as expected.
  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
  predicate {:axiom} EncryptionOutputEncryptedWithAAD(ciphertext: EncryptionOutput, aad: seq<uint8>)
  predicate {:axiom} CiphertextGeneratedWithPlaintext (ciphertext: seq<uint8>, plaintext: seq<uint8>)
  predicate {:axiom} EncryptedWithKey(ciphertext: seq<uint8>, key: seq<uint8>)
  predicate {:axiom} DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: AES_GCM): (encArt: EncryptionOutput)
    requires |s| >= encAlg.tagLength as int
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLength as int
  {
    EncryptionOutput(s[.. |s| - encAlg.tagLength as int], s[|s| - encAlg.tagLength as int ..])
  }

  method {:extern "AESEncryption.AES_GCM", "AESEncryptExtern"} AESEncryptExtern(encAlg: AES_GCM, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res : Result<EncryptionOutput, string>)
    requires |iv| == encAlg.ivLength as int
    requires |key| == encAlg.keyLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)

  method AESEncrypt(encAlg: AES_GCM, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res : Result<EncryptionOutput, string>)
    requires |iv| == encAlg.ivLength as int
    requires |key| == encAlg.keyLength as int
    ensures res.Success? ==>
      |res.value.cipherText| == |msg| && |res.value.authTag| == encAlg.tagLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)
    // This is useful information to have to prove correctness
    ensures res.Success? ==> |res.value.authTag| == encAlg.tagLength as nat
    {
      res := AESEncryptExtern(encAlg, iv, key, msg, aad);
      if (res.Success? && |res.value.cipherText| != |msg|){
        res := Failure("AESEncrypt did not return cipherText of expected length");
      }
      if (res.Success? && |res.value.authTag| != encAlg.tagLength as int){
        res := Failure("AESEncryption did not return valid tag");
      }
    }

  method {:extern "AESEncryption.AES_GCM", "AESDecryptExtern"} AESDecryptExtern(encAlg: AES_GCM, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |key| == encAlg.keyLength as int
    requires |iv| == encAlg.ivLength as int
    requires |authTag| == encAlg.tagLength as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)

  method AESDecrypt(encAlg: AES_GCM, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |key| == encAlg.keyLength as int
    requires |iv| == encAlg.ivLength as int
    requires |authTag| == encAlg.tagLength as int
    ensures res.Success? ==> |res.value| == |cipherTxt|
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    {
      res := AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);
      if (res.Success? && |cipherTxt| != |res.value|){
        res := Failure("AESDecrypt did not return plaintext of expected length");
      }
    }

}
