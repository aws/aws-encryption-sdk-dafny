include "../StandardLibrary/StandardLibrary.dfy"


// TODO: instantiate this
module {:extern "Signature"} Signature {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "ECDSAParams"} ECDSAParams = ECDSA_P384 | ECDSA_P256
    {
      function method SignatureLength(): uint16 {
        match this
        case ECDSA_P256 => 71
        case ECDSA_P384 => 103
      }
    }

    // TODO: I keep signatures as pairs (r,s) for now until I understand how they are encoded in the message header
    type Sig = (seq<uint8>, seq<uint8>)

    class {:extern "ECDSA"} ECDSA {

//        static function method MaxMsgLen (s : ECDSAParams) : Option<nat> { None }

        static predicate {:axiom} WfSig (s : ECDSAParams, sig : Sig)
        static predicate {:axiom} WfSK (s : ECDSAParams, sk : seq<uint8>)
        static predicate {:axiom} WfVK (s : ECDSAParams, vk : seq<uint8>)
        static predicate {:axiom} IsSignKeypair (s : ECDSAParams, sk : seq<uint8>, vk : seq<uint8>)

        /*
        static function method VKOfSK (s : ECDSAParams, sk : seq<uint8>) : (vk : seq<uint8>)
            requires WfSK(s, sk)
            ensures WfVK(s, vk)
            ensures IsSignKeypair(s, sk, vk)
            */

        static method {:extern "KeyGen"} KeyGen(s : ECDSAParams) returns (res : Option<(seq<uint8>, seq<uint8>)>)
            ensures res.Some? ==> WfSK(s, res.get.1)
            ensures res.Some? ==> WfVK(s, res.get.0)
            ensures res.Some? ==> IsSignKeypair(s, res.get.1, res.get.0)
//            ensures VKOfSK(s, sk) == vk

    }

    method {:extern "Signature.ECDSA", "Sign"} Sign(s: ECDSAParams, key: seq<uint8>, digest: seq<uint8>) returns (sig: Option<seq<uint8>>)
      requires ECDSA.WfSK(s, key)
      ensures sig.Some? ==> |sig.get| == s.SignatureLength() as int
      // ensures sig.Some? ==> WfSig(s, sig.get)
      // ensures sig.Some? ==> forall vk :: WfVK(s, vk) ==> IsSignKeypair(s, sk, vk) ==> Verify(s, vk, m, sig.get) == true

    function method {:extern "Signature.ECDSA", "Verify"} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>): bool
      // requires ECDSA.WfVK(s, key)
      // requires MaxMsgLen(s).Some? ==> |msg| <= MaxMsgLen(s).get
      // requires WfSig(s, sig)

    method {:extern "Signature.ECDSA", "Digest"} Digest(s: ECDSAParams, msg: seq<uint8>) returns (digest: seq<uint8>)
}
