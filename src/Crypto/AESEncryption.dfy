include "../SDK/AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "EncryptionSuites.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import EncryptionSuites
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, EncryptionSuites, StandardLibrary, UInt, PlaintextDecryptedWithAAD, EncryptionOutputEncryptedWithAAD
    reveals EncryptionOutput

  datatype EncryptionOutput = EncryptionOutput(cipherText: seq<uint8>, authTag: seq<uint8>)

  // The following are used to tie plaintext and ciphertext with the AAD that was used to produce them.
  // These are assumptions which should ultimately come from our externs, which can be referenced elsewhere
  // in order to ensure that the AAD used is as expected.
  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
  predicate {:axiom} EncryptionOutputEncryptedWithAAD(ciphertext: EncryptionOutput, aad: seq<uint8>)

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: EncryptionSuites.EncryptionSuite): (encArt: EncryptionOutput)
    requires encAlg.Valid()
    requires |s| >= encAlg.tagLen as int
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLen as int
  {
    EncryptionOutput(s[.. |s| - encAlg.tagLen as int], s[|s| - encAlg.tagLen as int ..])
  }

  method {:extern "AESEncryption.AES_GCM", "AESEncrypt"} AESEncrypt(encAlg: EncryptionSuites.EncryptionSuite, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res : Result<EncryptionOutput>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |iv| == encAlg.ivLen as int
    requires |key| == encAlg.keyLen as int
    ensures res.Success? ==>
      |res.value.cipherText| == |msg| && |res.value.authTag| == encAlg.tagLen as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)

  method {:extern "AESEncryption.AES_GCM", "AESDecrypt"} AESDecrypt(encAlg: EncryptionSuites.EncryptionSuite, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |key| == encAlg.keyLen as int
    requires |iv| == encAlg.ivLen as int
    requires |authTag| == encAlg.tagLen as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
}
