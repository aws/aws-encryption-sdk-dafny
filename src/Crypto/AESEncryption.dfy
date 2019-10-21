include "../SDK/AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "EncryptionAlgorithms.dfy"
include "GenBytes.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import EncryptionAlgorithms
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, EncryptionAlgorithms, StandardLibrary, UInt
    reveals EncryptionOutput

  // Is there a better name/location for this?
  datatype EncryptionOutput = EncryptionOutput(cipherText: seq<uint8>, authTag: seq<uint8>)

  function method EncryptionArtifactFromByteSeq(s: seq<uint8>, p: EncryptionAlgorithms.Params): (encArt: EncryptionOutput)
    requires p.Valid()
    requires |s| >= p.tagLen as int
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == p.tagLen as int
  {
    EncryptionOutput(s[.. |s| - p.tagLen as int], s[|s| - p.tagLen as int ..])
  }

  method {:extern "AESEncryption.AES_GCM", "AESEncrypt"} AESEncrypt(params: EncryptionAlgorithms.Params, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res : Result<EncryptionOutput>)
    requires params.Valid()
    requires params.alg.AES?
    requires params.alg.mode.GCM?
    requires |iv| == params.ivLen as int
    requires |key| == params.keyLen as int
    ensures res.Success? ==> |res.value.authTag| == params.tagLen as int

  method {:extern "AESEncryption.AES_GCM", "AESDecrypt"} AESDecrypt(params: EncryptionAlgorithms.Params, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>>)
    requires params.Valid()
    requires params.alg.AES?
    requires params.alg.mode.GCM?
    requires |key| == params.keyLen as int
    requires |iv| == params.ivLen as int 
    requires |authTag| == params.tagLen as int
}
