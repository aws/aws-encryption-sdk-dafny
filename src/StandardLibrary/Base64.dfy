include "StandardLibrary.dfy"
include "UInt.dfy"

module Base64 {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    newtype index = x | 0 <= x < 0x40

    predicate method IsBase64Char(c: char) {
        var i := c as int;
        i == 43 || 47 <= i <= 57 || 65 <= i <= 90 || 97 <= i <= 122
    }

    predicate method IsUnpaddedBase64String(s: string) {
        |s| % 4 == 0 && forall k :: k in s ==> IsBase64Char(k)
    }

    function method Base64Char(i: index): (c: char)
        ensures IsBase64Char(c)
    {
        if i == 63 then '/'
        else if i == 62 then '+'
        else if 52 <= i <= 61 then (i as int - 4) as char
        else if 26 <= i <= 51 then (i as int + 71) as char
        else (i as int + 65) as char
    }

    function method Base64Inv(c: char): (i: index)
        requires IsBase64Char(c)
        ensures Base64Char(i) == c
    {
        if c == '/' then 63
        else if c == '+' then 62
        else if 48 <= c as int <= 57 then (c as int + 4) as index
        else if 65 <= c as int <= 90 then (c as int - 65) as index
        else (c as int - 71) as index
    }

    function method SplitBytes(n: int): (b: (uint8, uint8, uint8))
        requires 0 <= n < 0x100_0000
    {
        var n0 := n / 0x1_0000;
        var m0 := n - n0 * 0x1_0000;
        var n1 := m0 / 0x100;
        var m1 := m0 - n1 * 0x100;
        var n2 := m1;
        assert n0 * 0x1_0000 + n1 * 0x100 + n2 == n;
        (n0 as uint8, n1 as uint8, n2 as uint8)
    }

    function method CombineBytes(b: (uint8, uint8, uint8)): (n: int)
        ensures 0 <= n < 0x100_0000
        ensures SplitBytes(n) == b
    {
        b.0 as int * 0x1_0000 + b.1 as int * 0x100 + b.2 as int
    }

    function method CombineIndices(c: (index, index, index, index)): (n: int)
        ensures 0 <= n < 0x100_0000
    {
        c.0 as int * 0x4_0000 + c.1 as int * 0x1000 + c.2 as int * 0x40 + c.3 as int
    }

    function method SplitIndices(n: int): (c: (index, index, index, index))
        requires 0 <= n < 0x100_0000
        ensures CombineIndices(c) == n
    {
        var n0 := n / 0x4_0000;
        var m0 := n - n0 * 0x4_0000;
        var n1 := m0 / 0x1000;
        var m1 := m0 - n1 * 0x1000;
        var n2 := m1 / 0x40;
        var m2 := m1 - n2 * 0x40;
        var n3 := m2;
        assert n0 * 0x4_0000 + n1 * 0x1000 + n2 * 0x40 + n3 == n;
        (n0 as index, n1 as index, n2 as index, n3 as index)
    }

    function method DecodeBlock(c: (index, index, index, index)): (b: (uint8, uint8, uint8)) {
        SplitBytes(CombineIndices(c))
    }

    function method EncodeBlock(b: (uint8, uint8, uint8)): (c: (index, index, index, index))
        ensures DecodeBlock(c) == b
    {
        SplitIndices(CombineBytes(b))
    }

    function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
        requires |s| % 4 == 0
        ensures |b| == |s| / 4 * 3
        ensures |b| % 3 == 0
    {
        if |s| == 0 then [] else
        var d := DecodeBlock((s[0], s[1], s[2], s[3]));
        [d.0, d.1, d.2] + DecodeRecursively(s[4..])
    }

    function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
        requires |b| % 3 == 0
        ensures |s| == |b| / 3 * 4
        ensures |s| % 4 == 0
        ensures DecodeRecursively(s) == b
    {
        if |b| == 0 then [] else
        var e := EncodeBlock((b[0], b[1], b[2]));
        [e.0, e.1, e.2, e.3] + EncodeRecursively(b[3..])
    }

    function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
        requires forall k :: k in s ==> IsBase64Char(k)
        ensures |b| == |s|
        ensures forall k :: 0 <= k < |b| ==> Base64Char(b[k]) == s[k]
    {
        // if |s| == 0 then [] else
        // [Base64Inv(s[0])] + FromCharsToIndices(s[1..])
        seq(|s|, i requires 0 <= i < |s| => Base64Inv(s[i]))
    }

    function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
        ensures forall k :: k in s ==> IsBase64Char(k)
        ensures |s| == |b|
        ensures forall k :: 0 <= k < |s| ==> Base64Inv(s[k]) == b[k]
        ensures FromCharsToIndices(s) == b
    {
        // if |b| == 0 then "" else
        // [Base64Char(b[0])] + FromIndicesToChars(b[1..])
        seq(|b|, i requires 0 <= i < |b| => Base64Char(b[i]))
    }

    function method DecodeConverter(s: seq<char>): (b: seq<uint8>)
        requires IsUnpaddedBase64String(s)
        ensures |b| == |s| / 4 * 3
        ensures |b| % 3 == 0
    {
        DecodeRecursively(FromCharsToIndices(s))
    }

    function method {:opaque} EncodeConverter(b: seq<uint8>): (s: seq<char>)
        requires |b| % 3 == 0
        ensures IsUnpaddedBase64String(s)
        ensures |s| == |b| / 3 * 4
        ensures DecodeConverter(s) == b
    {
        FromIndicesToChars(EncodeRecursively(b))
    }

    predicate method Is1Padding(s: seq<char>) {
        |s| == 4 &&
        IsBase64Char(s[0]) &&
        IsBase64Char(s[1]) &&
        IsBase64Char(s[2]) && Base64Inv(s[2]) % 0x4 == 0 &&
        s[3] == '='
    }

    function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
        requires Is1Padding(s)
        ensures |b| == 2
    {
        var c := (s[0], s[1], s[2], 'A');
        var d := DecodeBlock((Base64Inv(c.0), Base64Inv(c.1), Base64Inv(c.2), Base64Inv(c.3)));
        [d.0, d.1]
    }

    function method {:opaque} Encode1Padding(b: seq<uint8>): (s: seq<char>)
        requires |b| == 2
        ensures Is1Padding(s)
        ensures Decode1Padding(s) == b
    {
        var e := EncodeBlock((b[0], b[1], 0));
        [Base64Char(e.0), Base64Char(e.1), Base64Char(e.2), '=']
    }

    predicate method Is2Padding(s: seq<char>) {
        |s| == 4 &&
        IsBase64Char(s[0]) &&
        IsBase64Char(s[1]) && Base64Inv(s[1]) % 0x10 == 0 &&
        s[2] == '=' &&
        s[3] == '='
    }

    function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
        requires Is2Padding(s)
    {
        var c := (s[0], s[1], 'A', 'A');
        var d := DecodeBlock((Base64Inv(c.0), Base64Inv(c.1), Base64Inv(c.2), Base64Inv(c.3)));
        [d.0]
    }

    function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
        requires |b| == 1
        ensures Is2Padding(s)
        ensures Decode2Padding(s) == b
    {
        var e := EncodeBlock((b[0], 0, 0));
        [Base64Char(e.0), Base64Char(e.1), '=', '=']
    }

    predicate method IsBase64String(s: string) {
        && |s| % 4 == 0
        && (|| IsUnpaddedBase64String(s)
            || (&& IsUnpaddedBase64String(s[..|s|-4])
                && (|| Is2Padding(s[|s|-4..])
                    || Is1Padding(s[|s|-4..]))))
    }

    function method DecodeValid(s: seq<char>): (b: seq<uint8>)
        requires IsBase64String(s)
    {
        if s == [] then []
        else if Is2Padding(s[|s|-4..]) then DecodeConverter(s[..|s|-4]) + Decode2Padding(s[|s|-4..])
        else if Is1Padding(s[|s|-4..]) then DecodeConverter(s[..|s|-4]) + Decode1Padding(s[|s|-4..])
        else DecodeConverter(s)
    }

    function method Decode(s: seq<char>): (b: Result<seq<uint8>>) {
        if IsBase64String(s) then Success(DecodeValid(s)) else Failure("The encoding is malformed")
    }

    function method Encode(b: seq<uint8>): (s: seq<char>)
        ensures Decode(s) == Success(b)
        ensures StringIs8Bit(s)
    {
        var res := (
            if |b| % 3 == 0 then EncodeConverter(b)
            else if |b| % 3 == 1 then EncodeConverter(b[..|b|-1]) + Encode2Padding(b[|b|-1..])
            else EncodeConverter(b[..|b|-2]) + Encode1Padding(b[|b|-2..])
        );
        assert DecodeValid(res) == b;
        res
    }

    function method DecodeFromByteSeq(s: seq<uint8>): Result<seq<uint8>> {
      Decode(ByteSeqToString(s))
    }

    function method EncodeToByteSeq(b: seq<uint8>): seq<uint8> {
      StringToByteSeq(Encode(b))
    }

    method TestBase64(msg: string, expected: string)
        requires forall k :: 0 <= k < |msg| ==> 0 <= msg[k] as int < 0x100
    {
        print "The message is: ", msg, "\n";

        var uint8Msg: seq<uint8> := [];
        var i := 0;
        while i < |msg| {
            uint8Msg := uint8Msg + [msg[i] as int as uint8];
            i := i + 1;
        }
        var encoded := Encode(uint8Msg);
        print "The encoding is: ", encoded, "\n";
        print "The expected is: ", expected, "\n";
        print "The encoding ", (if encoded == expected then "matches" else "doesn't match"), " the expected.\n";

        var decoded := Decode(encoded);
        assert decoded.value == uint8Msg;

        var dmsg := "";
        i := 0;
        while i < |decoded.value| {
            dmsg := dmsg + [decoded.value[i] as int as char];
            i := i + 1;
        }
        print "The decoded message is: ", dmsg, "\n\n";
    }

    /*method Main() {
        // TEST 0: No padding
        TestBase64("Hello I am a string with no padding.", "SGVsbG8gSSBhbSBhIHN0cmluZyB3aXRoIG5vIHBhZGRpbmcu");
        // TEST 1: One padding
        TestBase64("Hi, I am a string with one padding.", "SGksIEkgYW0gYSBzdHJpbmcgd2l0aCBvbmUgcGFkZGluZy4=");
        // TEST 2: Two paddings
        TestBase64("Hello I'm a string with two paddings.", "SGVsbG8gSSdtIGEgc3RyaW5nIHdpdGggdHdvIHBhZGRpbmdzLg==");
    }*/
}
