include "../StandardLibrary/StandardLibrary.dfy"


// TODO: instantiate this
module {:extern "Signature"} Signature { 
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "Msg"} Msg = Msg(m: seq<uint8>)
    datatype {:extern "SigningKey"} SigningKey = SK(k : seq<uint8>)
    datatype {:extern "VerifKey"} VerifKey = VK(k : seq<uint8>)
    datatype {:extern "Sig"} Sig = Sig(c : seq<uint8>)

    datatype ECDSAParams = ECDSA_P384 | ECDSA_P256

    function method MaxMsgLen (s : ECDSAParams) : Option<nat> { None }
    function method VKLen (s : ECDSAParams) : nat { 0 }
    predicate WfSig (s : ECDSAParams, sig : Sig) { true }
    predicate WfSK (s : ECDSAParams, sk : SigningKey) { true }
    predicate WfVK (s : ECDSAParams, vk : VerifKey) { |vk.k| == VKLen(s) && true }
    predicate IsSignKeypair (s : ECDSAParams, sk : SigningKey, vk : VerifKey) { true }

    function method VKOfSK (s : ECDSAParams, sk : SigningKey) : (vk : VerifKey)
        requires WfSK(s, sk)
        ensures WfVK(s, vk)
        ensures IsSignKeypair(s, sk, vk) {
            VK([])
        }

    method KeyGen(s : ECDSAParams) returns (sk : SigningKey, vk : VerifKey)
        ensures WfSK(s, sk)
        ensures WfVK(s, vk)
        ensures IsSignKeypair(s, sk, vk)
        ensures VKOfSK(s, sk) == vk {
            sk := SK([]);
            vk := VK([]);
        }

    function method Verify(s : ECDSAParams, vk : VerifKey, m : Msg, sig : Sig) : bool
        requires WfVK(s, vk)
        requires MaxMsgLen(s).Some? ==> |m.m| <= MaxMsgLen(s).get
        requires WfSig(s, sig) {
            true
        }

    method Sign(s : ECDSAParams, sk : SigningKey, m : Msg) returns (sig : Option<Sig>)
        requires WfSK(s, sk)
        requires MaxMsgLen(s).Some? ==> |m.m| <= MaxMsgLen(s).get
        ensures sig.Some? ==> WfSig(s, sig.get)
        ensures sig.Some? ==> forall vk :: WfVK(s, vk) ==> IsSignKeypair(s, sk, vk) ==> Verify(s, vk, m, sig.get) == true {

        }
}