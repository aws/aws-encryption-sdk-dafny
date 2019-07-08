include "../Util/StandardLibrary.dfy"

module {:extern "RNGWrap"} RNG {
    import opened StandardLibrary
    class {:extern} GenBytesClass {
        method {:extern} GenUniformArray(i : uint16) returns (o : array<byte>) ensures o.Length == i as nat
        method {:extern} GenUniformSeq(i : uint16) returns (o : seq<byte>) ensures |o| == i as nat
        constructor {:extern} ()
    }

    method GenBytes(i : uint16) returns (o : seq<byte>) ensures |o| == i as nat {
        var x := new GenBytesClass();
        o := x.GenUniformSeq(i);
    }
}