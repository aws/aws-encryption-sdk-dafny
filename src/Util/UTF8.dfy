include "StandardLibrary.dfy"

// Provides a function ValidUTF8 which checks if an array of bytes is a valid sequence of UTF8 code points.
// Each code point of a UTF8 string is one of the following variants, ranging from one to four bytes:
// Case 1 : 0xxxxxxx
// Case 2 : 110xxxxx 10xxxxxx
// Case 3 : 1110xxxx 10xxxxxx 10xxxxxx
// Case 4 : 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx

// The first byte of each code point is called the leading byte, while the rest are called continuation bytes.

// This does NOT perform any range checks on the values encoded.

module UTF8 {
    import opened StandardLibrary

    // Returns the value of the idx'th bit, from least to most significant bit (0- indexed)
    function method bit_at (x: byte, idx: byte): bool
    requires idx < 8
    {
    var w := x as bv8;
    (w >> idx) & 1 == 1
    }

    // Checks if a[offset] is a valid continuation byte.
    predicate method ValidUTF8Continuation (a : array<byte>, offset : nat)
        reads a
        requires a.Length > offset 
    {
            bit_at(a[offset], 7) && !bit_at(a[offset], 6)
    }

    // Returns which leading byte is at a[offset], or 0 if it is not a leading byte.
    function method CodePointCase (a : array<byte>, offset: nat)  : byte
        reads a
        requires offset < a.Length
    {

        if bit_at(a[offset], 7) then // 1xxxxxxx
            if bit_at(a[offset], 6) then //11xxxxxx
                if bit_at(a[offset], 5) then // 111xxxxx
                    if bit_at(a[offset], 4) then // 1111xxxx
                        if bit_at(a[offset], 3) then // 11111xxx
                            0 // Error case
                        else // 11110xxx
                            4 
                    else // 1110xxxx 
                        3
                else // 110xxxx
                    2
            else //10xxxxxx
                0 // Error case
        else //0xxxxxxx
            1
    }

    predicate method ValidUTF8_at (a : array<byte>, offset : nat)
        reads a 
        requires offset <= a.Length
        decreases (a.Length - offset)
    {
        if offset == a.Length then true else
        var c := CodePointCase(a, offset);
        if c == 1 then 
            ValidUTF8_at(a, offset + 1)
        else if c == 2 then
            !bit_at(a[offset], 3) && 
            a.Length >= offset + 2 && 
            ValidUTF8Continuation(a, offset + 1) && 
            ValidUTF8_at(a, offset + 2)
        else if c == 3 then
            !bit_at(a[offset], 4) && 
            a.Length >= offset + 3 && 
            ValidUTF8Continuation(a, offset + 1) && 
            ValidUTF8Continuation(a, offset + 2) && 
            ValidUTF8_at(a, offset + 3) 
        else  // c == 4
            !bit_at(a[offset], 3) && 
            a.Length >= offset + 4 && 
            ValidUTF8Continuation(a, offset + 1) && 
            ValidUTF8Continuation(a, offset + 2) && 
            ValidUTF8Continuation(a, offset + 3) && 
            ValidUTF8_at(a, offset + 4)
    }

    predicate method ValidUTF8 (a : array<byte>)
        reads a
    {
        ValidUTF8_at(a, 0)
    }

}