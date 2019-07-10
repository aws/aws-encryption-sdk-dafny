include "../StandardLibrary/StandardLibrary.dfy"
include "Cipher.dfy"
include "GenBytes.dfy"
include "EncryptionDefs.dfy"
include "AESEncryption.dfy"
include "RSAEncryption.dfy"

module {:extern "Encryption"} Encryption { 
    import C = Cipher
    import opened StandardLibrary
    import opened EncDefs
    import opened AESEncryption
    import opened RSAEncryption

    // Currently I use datatypes with methods instead of singletons (because they don't exist)
    datatype EncType = EncRSA(bits : RSABitLength, padding : RSAPaddingMode) | EncAES(C.CipherParams)

    function method MaxMsgLen(e : EncType) : Option<nat>  {
        match e
            case EncAES(_) => None
            case EncRSA(b, p) => RSA.msg_len_of_rsa_params(p, b)
    }

    predicate WfCtx (e : EncType, c : Ctx) {
        match e
            case EncRSA(bits, padding) => RSA.RSAWfCtx(bits, padding, c)
            case EncAES(p) => AES.AESWfCtx(p, c)
    }

    predicate WfEK (e : EncType, ek : EncryptionKey) {
        match e
            case EncRSA(b, p) => RSA.RSAWfEK(b, p, ek)
            case EncAES(p) => AES.AESWfEK(p, ek)
    }

    predicate WfDK (e : EncType, dk : DecryptionKey) {
        match e
            case EncRSA(b, p) => RSA.RSAWfDK(b, p, dk)
            case EncAES(p) => AES.AESWfDK(p, dk)
    }

    predicate IsKeypair(e : EncType, ek : EncryptionKey, dk :DecryptionKey) {
        match e
            case EncRSA(b,p) => RSA.IsRSAKeypair(b, p, ek, dk)
            case EncAES(p) => AES.IsAESKeypair(ek, dk)
    }

    method KeyGen(e : EncType) returns (ek : EncryptionKey, dk : DecryptionKey)
        ensures WfEK(e, ek)
        ensures WfDK(e, dk)
        ensures IsKeypair(e, ek, dk) {
            match e
                case EncRSA(b, p) => ek, dk := RSA.RSAKeygen(b, p);
                case EncAES(p) => ek, dk := AES.AESKeygen(p);
        }

    // If the encryption scheme does not use AAD, the md parameter is ignored
    function method Decrypt(e : EncType, dk : DecryptionKey, md : MData, c : Ctx) : Option<Msg>
        requires WfDK(e, dk)
        requires WfCtx(e, c) {
            match e
                case EncRSA(b, p) => RSA.RSADecrypt(b, p, dk, md, c)
                case EncAES(p) => AES.AESDecrypt(p, dk, md, c)
        }

    method Encrypt(e : EncType, ek : EncryptionKey, msg : Msg, md : MData) returns (c : Option<Ctx>)
        requires WfEK(e, ek)
        requires forall o :: MaxMsgLen(e) == Some(o) ==> |msg.m| <= o
        ensures c.Some? ==> WfCtx(e,c.get)
        ensures c.Some? ==> forall dk :: IsKeypair(e, ek, dk) ==> WfDK(e, dk) ==> Decrypt(e, dk, md, c.get) == Some(msg) {
            match e
                case EncRSA(b, p) => c := RSA.RSAEncrypt(b, p, ek, msg, md);
                case EncAES(p) => c := AES.AESEncrypt(p, ek, msg, md);
        }

}