include "../Util/StandardLibrary.dfy"
include "Cipher.dfy"

module {:extern "EncDefs"} EncDefs {
    import C = Cipher
    import opened StandardLibrary
    datatype {:extern "Msg"} Msg = Msg(m: seq<byte>)
    datatype {:extern "EncryptionKey"} EncryptionKey = EK(k : seq<byte>)
    datatype {:extern "DecryptionKey"} DecryptionKey = DK(k : seq<byte>)
    datatype {:extern "MData"} MData = MD(md : seq<byte>) 
    datatype {:extern "Ctx"} Ctx = Ctx(c : seq<byte>)
}