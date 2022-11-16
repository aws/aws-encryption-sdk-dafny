// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "StandardLibrary.dfy"
include "UInt.dfy"
include "Base64.dfy"

module Base64Lemmas {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened Base64

  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures Encode(DecodeValid(s)) == s
  {}

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[(|s| - 4)..])
    requires !Is2Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      Encode(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeUnpadded(s));
    == { DecodeEncodeUnpadded(s); }
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[..(|DecodeValid(s)| - 2)] == DecodeUnpadded(s[..(|s| - 4)])
  {}

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[(|DecodeValid(s)| - 2)..] == Decode1Padding(s[(|s| - 4)..])
  {}

  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 2;
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 2)]) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValidUnpaddedPartialFrom1PaddedSeq(s); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValid1PaddedPartialFrom1PaddedSeq(s); }
      s[..(|s| - 4)] + Encode1Padding(Decode1Padding(s[(|s| - 4)..]));
    == { DecodeEncode1Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    == { SeqPartsMakeWhole(s, (|s| - 4)); }
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[..(|DecodeValid(s)| - 1)] == DecodeUnpadded(s[..(|s| - 4)])
  {}

  lemma DecodeValid2PaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[(|DecodeValid(s)| - 1)..] == Decode2Padding(s[(|s| - 4)..])
  {}

  lemma DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 1;
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 1)]) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValidUnpaddedPartialFrom2PaddedSeq(s); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValid2PaddedPartialFrom2PaddedSeq(s); }
      s[..(|s| - 4)] + Encode2Padding(Decode2Padding(s[(|s| - 4)..]));
    == { DecodeEncode2Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    == { SeqPartsMakeWhole(s, (|s| - 4)); }
      s;
    }
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(DecodeValid(s)) == s
  {
    if s == [] {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeEmpty(s); }
        s;
      }
    } else if |s| >= 4 && Is1Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode1Padding(s); }
        s;
      }
    } else if |s| >= 4 && Is2Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode2Padding(s); }
        s;
      }
    } else {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeUnpadded(s); }
        s;
      }
    }
  }

  lemma EncodeDecodeValid(b: seq<uint8>)
    ensures DecodeValid(Encode(b)) == b
  {}

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
  {
    calc {
      Encode(Decode(s).value);
    == { DecodeValidEncode(s); }
      s;
    }
  }

  lemma EncodeDecode(b: seq<uint8>)
    ensures Decode(Encode(b)) == Success(b)
  {
    calc {
      Decode(Encode(b));
    == { assert IsBase64String(Encode(b)); }
      Success(DecodeValid(Encode(b)));
    == { EncodeDecodeValid(b); }
      Success(b);
    }
  }
}
