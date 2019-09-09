include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Digests"} Digests {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "HMAC_ALGORITHM"} HMAC_ALGORITHM = HmacSHA256 | HmacSHA384 | HmacNOSHA
  
    // Hash length in octets, e.g. HashLength(SHA256) = 256 = 32 * 8
    function {:axiom} HashLength(algorithm: HMAC_ALGORITHM): nat
        ensures algorithm == HmacSHA256 ==> HashLength(algorithm) == 32
        ensures algorithm == HmacSHA384 ==> HashLength(algorithm) == 48

    function {:axiom} Hash(algorithm: HMAC_ALGORITHM, key: seq<uint8>, message: seq<uint8>): seq<uint8>
        ensures |Hash(algorithm, key, message)| == HashLength(algorithm)
}