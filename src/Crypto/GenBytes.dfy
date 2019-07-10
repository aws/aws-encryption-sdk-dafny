include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "RNGWrap"} RNG {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    class {:extern} GenBytesClass {
        method {:extern} GenUniformArray(i : uint16) returns (o : array<uint8>) ensures o.Length == i as nat
        method {:extern} GenUniformSeq(i : uint16) returns (o : seq<uint8>) ensures |o| == i as nat
        constructor {:extern} ()
    }

    method GenBytes(i : uint16) returns (o : seq<uint8>) ensures |o| == i as nat {
        var x := new GenBytesClass();
        o := x.GenUniformSeq(i);
    }
}