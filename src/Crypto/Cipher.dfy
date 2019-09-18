include "../StandardLibrary/StandardLibrary.dfy"
include "GenBytes.dfy"

// Information about the ciphers in the Encryption SDK, as well as information common to all algorithms which use ciphers (both encryption and KDF).
module {:extern "Cipher"} Cipher {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened RNG

    datatype AESMode = AES256 | AES128 | AES192
    datatype {:extern "CipherParams"} CipherParams = CipherParams(mode: AESMode, keyLen: uint8, tagLen: uint8, ivLen: uint8)

    const MAX_KEY_LEN := 32
    const CIPHER_KEY_LENGTHS := {32, 24, 16};
    const TAG_LEN := 16 as uint8;
    const IV_LEN := 12 as uint8;

    const AES_GCM_128 := CipherParams(AES128, 16, TAG_LEN, IV_LEN);
    const AES_GCM_192 := CipherParams(AES192, 24, TAG_LEN, IV_LEN);
    const AES_GCM_256 := CipherParams(AES256, 32, TAG_LEN, IV_LEN);

    function method CipherOfKeyLength(n : int) : CipherParams
        requires n in CIPHER_KEY_LENGTHS {
            if n == 32 then AES_GCM_256
            else if n == 24 then AES_GCM_192
            else AES_GCM_128
        }

    function method KeyLengthOfCipher (c : CipherParams) : int {
        match c.mode
            case AES256 => 32
            case AES192 => 24
            case AES128 => 16
    }

    /*
    lemma Cipher_KeyLengthK (c : CipherParams)
        requires c.tagLen == TAG_LEN
        requires c.ivLen == IV_LEN
        ensures CipherOfKeyLength(KeyLengthOfCipher(c)) == c {
        match c.mode
            case AES256 =>
            case AES192 =>
            case AES128 =>
    }
    */

    method GenIV(m : CipherParams) returns (s : seq<uint8>) ensures |s| == m.ivLen as int {
            s := GenBytes(m.ivLen as uint16);
    }

    method GenKey(m : CipherParams) returns (s : seq<uint8>) ensures |s| == KeyLengthOfCipher(m) as int {
            s := GenBytes(KeyLengthOfCipher(m) as uint16);
    }


}
