include "../SDK/AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AESUtils.dfy"
include "WrappingAlgorithmSuite.dfy"
include "GenBytes.dfy"

module {:extern "AESEncryption"} AESEncryption {
  import AESUtils
  import WrappingAlgorithmSuite
  import RNG
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, AESUtils, StandardLibrary, UInt

  //FIXME: Ensure that these methods correctly handle authenticaition tags, see #36
  method AESDecrypt(params: AESUtils.Params, key: seq<uint8>, ctxt: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
    returns (res: Result<seq<uint8>>)
    requires |key| == params.keyLen as int
  {
    res := AES.AESDecrypt(params, key, ctxt, iv, aad);
  }

  method AESEncrypt(params: AESUtils.Params, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
    returns (res : Result<seq<uint8>>)
    requires |iv| == params.ivLen as int
    requires |key| == params.keyLen as int
    ensures res.Success? ==> params.tagLen as int < |res.value|
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
      returns (res : Result<seq<uint8>>)
      requires |iv| == params.ivLen as int
      requires |key| == params.keyLen as int
      ensures res.Success? ==> |res.value| > params.tagLen as int
  }
}
