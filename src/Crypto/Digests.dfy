include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Digests"} Digests {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "HMAC_ALGORITHM"} HMAC_ALGORITHM = HmacSHA256 | HmacSHA384 | HmacNOSHA

    // Hash length in octets (bytes), e.g. HashLength(SHA256) = 256 = 32 * 8
    function {:axiom} HashLength(algorithm: HMAC_ALGORITHM): (n: nat)
        ensures algorithm == HmacSHA256 ==> n == 32
        ensures algorithm == HmacSHA384 ==> n == 48

    function {:axiom} Hash(algorithm: HMAC_ALGORITHM, key: seq<uint8>, message: seq<uint8>): (s: seq<uint8>)
        ensures |s| == HashLength(algorithm)
}
