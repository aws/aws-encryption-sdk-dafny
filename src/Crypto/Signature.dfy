include "../StandardLibrary/StandardLibrary.dfy"


// TODO: instantiate this
module {:extern "Signature"} Signature { 
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "ECDSAParams"} ECDSAParams = ECDSA_P384 | ECDSA_P256

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

        static function method {:extern "Verify"} Verify(s : ECDSAParams, vk : seq<uint8>, m : seq<uint8>, sig : Sig) : bool
            requires WfVK(s, vk)
 //           requires MaxMsgLen(s).Some? ==> |m| <= MaxMsgLen(s).get
            requires WfSig(s, sig)

        static method {:extern "Sign"} Sign(s : ECDSAParams, sk : seq<uint8>, m : seq<uint8>) returns (sig : Option<Sig>)
            requires WfSK(s, sk)
  //          requires MaxMsgLen(s).Some? ==> |m| <= MaxMsgLen(s).get
            ensures sig.Some? ==> WfSig(s, sig.get)
            ensures sig.Some? ==> forall vk :: WfVK(s, vk) ==> IsSignKeypair(s, sk, vk) ==> Verify(s, vk, m, sig.get) == true 
    }
}