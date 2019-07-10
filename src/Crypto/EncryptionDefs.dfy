include "../StandardLibrary/StandardLibrary.dfy"
include "Cipher.dfy"

module {:extern "EncDefs"} EncDefs {
    import C = Cipher
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "Msg"} Msg = Msg(m: seq<uint8>)
    datatype {:extern "EncryptionKey"} EncryptionKey = EK(k : seq<uint8>)
    datatype {:extern "DecryptionKey"} DecryptionKey = DK(k : seq<uint8>)
    datatype {:extern "MData"} MData = MD(md : seq<uint8>) 
    datatype {:extern "Ctx"} Ctx = Ctx(c : seq<uint8>)
}