include "../SDK/AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AESUtils.dfy"
include "GenBytes.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import AESUtils
  import RNG
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, AESUtils, StandardLibrary, UInt
    reveals EncryptionArtifacts, EncryptionArtifactFromByteSeq

  // Is there a better name/location for this?
  datatype EncryptionArtifacts = EncryptionArtifacts(cipherText: seq<uint8>, authTag: seq<uint8>)

  function method EncryptionArtifactFromByteSeq(s: seq<uint8>, p: AESUtils.Params): (encArt: EncryptionArtifacts)
    requires p.tagLen > 0
    requires |s| > p.tagLen as int
    ensures |encArt.cipherText + encArt.authTag| <= |s|
    ensures |encArt.authTag| == p.tagLen as int
  {
    EncryptionArtifacts(s[.. |s| - p.tagLen as int], s[|s| - p.tagLen as int ..])
  }

  method AESDecrypt(params: AESUtils.Params, key: seq<uint8>, encryptionArtifacts: EncryptionArtifacts, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>>)
    requires |key| == params.keyLen as int
    requires |encryptionArtifacts.authTag| == params.tagLen as int
  {
    var cipherText := encryptionArtifacts.cipherText + encryptionArtifacts.authTag;
    res := AES.AESDecrypt(params, key, cipherText, iv, aad);
  }

  method AESEncrypt(params: AESUtils.Params, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res : Result<EncryptionArtifacts>)
    requires |iv| == params.ivLen as int
    requires |key| == params.keyLen as int
    ensures res.Success? ==> |res.value.authTag| == params.tagLen as int
  {
    res := AES.AESEncrypt(params, iv, key, msg, aad);
  }

  class {:extern "AES_GCM"} AES {
    static method {:extern "AESDecrypt"} AESDecrypt(params: AESUtils.Params,
                                                    key: seq<uint8>,
                                                    ctxt: seq<uint8>,
                                                    iv: seq<uint8>,
                                                    aad: seq<uint8>)
        returns (res: Result<seq<uint8>>)
      requires |key| == params.keyLen as int

    static method {:extern "AESEncrypt"} AESEncrypt (params: AESUtils.Params,
                                                      iv : seq<uint8>,
                                                      key : seq<uint8>,
                                                      msg : seq<uint8>,
                                                      aad : seq<uint8>)
        returns (res : Result<EncryptionArtifacts>)
      requires |iv| == params.ivLen as int
      requires |key| == params.keyLen as int
    ensures res.Success? ==> |res.value.authTag| == params.tagLen as int
  }
}
