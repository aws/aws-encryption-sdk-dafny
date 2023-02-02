// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsEncryptionSdkTypes.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"

module EncryptionContext {
  import Seq
  import StandardLibrary
  import Sets
  import opened SerializableTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  // There needs to be a canonical representation of the encryption context.
  // Once the encryption context has been serialized,
  // then the bytes in the message can provide this canonical representation.
  // However, it is best if a canonical representation exists.
  // For reading and writing, we use the arbitrary given order,
  // and separate the ordering problem from serialization.
  type ESDKEncryptionContextPair = p: Pair<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  |
    && HasUint16Len(p.key) && ValidUTF8Seq(p.key)
    && HasUint16Len(p.value) && ValidUTF8Seq(p.value)
  witness *

  type ESDKCanonicalEncryptionContext = pairs: seq<ESDKEncryptionContextPair>
  | ESDKCanonicalEncryptionContext?(pairs)
  witness *

  predicate ESDKCanonicalEncryptionContext?(pairs: seq<ESDKEncryptionContextPair>) {
    && HasUint16Len(pairs)
    && LinearLength(pairs) < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
    //= compliance/data-format/message-header.txt#2.5.1.7.2.2
    //= type=implication
    //# This sequence MUST NOT contain duplicate entries.
    && KeysAreUnique(pairs)
  }

  predicate KeysAreUnique<K, V>(pairs: Linear<K, V>)
  {
    (forall i, j
    // This satisfies every cardinality AND i != j
    :: 0 <= i < j < |pairs|
    ==> pairs[i].key != pairs[j].key)
  }

  function method GetCanonicalEncryptionContext(
    encryptionContext: ESDKEncryptionContext
  )
    :(ret: ESDKCanonicalEncryptionContext)
    ensures |encryptionContext| == 0 ==> |ret| == 0
  {
    GetCanonicalLinearPairs(encryptionContext)
  }

  function method GetEncryptionContext(
    canonicalEncryptionContext: ESDKCanonicalEncryptionContext
  )
    :(ret: MPL.EncryptionContext)
    ensures |canonicalEncryptionContext| == 0 ==> |ret| == 0
  {
    // This is needed because Dafny can not reveal the subset type by default?
    assert ESDKCanonicalEncryptionContext?(canonicalEncryptionContext);
    assert KeysAreUnique(canonicalEncryptionContext);
    map i
    | 0 <= i < |canonicalEncryptionContext|
    :: canonicalEncryptionContext[i].key := canonicalEncryptionContext[i].value
  }

  lemma LemmaCardinalityOfEncryptionContextEqualsPairs(
    pairs: ESDKCanonicalEncryptionContext,
    ec: MPL.EncryptionContext
  )
    requires ec == GetEncryptionContext(pairs)
    ensures |ec| == |pairs|
  {
    if |pairs| == 0 {
    } else {
      var front := Seq.DropLast(pairs);
      var tail := Seq.Last(pairs);
      var ecOfFront := GetEncryptionContext(front);
      assert pairs == front + [tail];
      assert ec.Keys == ecOfFront.Keys + {tail.key};

      assert |ecOfFront.Keys| == |ecOfFront|;
      LemmaCardinalityOfEncryptionContextEqualsPairs(front, ecOfFront);
    }
  }

  lemma  {:vcs_split_on_every_assert} LemmaLengthOfPairsEqualsEncryptionContext(
    pairs: ESDKCanonicalEncryptionContext,
    ec: MPL.EncryptionContext
  )
    requires ec == GetEncryptionContext(pairs)
    ensures LinearLength(pairs) == Length(ec)
  {
    if |pairs| == 0 {
    } else {
      var front := Seq.DropLast(pairs);
      var tail := Seq.Last(pairs);
      var ecOfFront := GetEncryptionContext(front);

      assert pairs == front + [tail];
      assert ec.Keys == ecOfFront.Keys + {tail.key};
      assert ec == ecOfFront + map[tail.key := tail.value];
      assert |ecOfFront.Keys| == |ecOfFront|;

      assert LinearLength(pairs) == Length(ec);

      LemmaLengthOfPairsEqualsEncryptionContext(front, ecOfFront);
      LinearLengthIsDistributive(front, [tail]);
    }

  }

  lemma LemmaESDKCanonicalEncryptionContextIsESDKEncryptionContext(
    pairs: ESDKCanonicalEncryptionContext,
    ec: MPL.EncryptionContext
  )
    requires ec == GetEncryptionContext(pairs)
    ensures IsESDKEncryptionContext(ec)
  {
    LemmaCardinalityOfEncryptionContextEqualsPairs(pairs, ec);
    LemmaLengthOfPairsEqualsEncryptionContext(pairs, ec);
  }

  //= compliance/data-format/message-header.txt#2.5.1.7
  //# The following table describes the fields that form the AAD.  The
  //# bytes are appended in the order shown.
  //#
  //#  +=================+==============================+================+
  //#  | Field           | Length (bytes)               | Interpreted as |
  //#  +=================+==============================+================+
  //#  | Key Value Pairs | 2                            | UInt16         |
  //#  | Length (Section |                              |                |
  //#  | 2.5.1.7.1)      |                              |                |
  //#  +-----------------+------------------------------+----------------+
  //#  | Key Value Pairs | Variable.  Determined by the | Key Value      |
  //#  | (Section        | value of Key Value Pairs     | Pairs (Section |
  //#  | 2.5.1.7.2)      | Length (Section 2.5.1.7.1).  | 2.5.1.7.2)     |
  //#  +-----------------+------------------------------+----------------+
  function method WriteAADSection(
    ec: ESDKCanonicalEncryptionContext
  ):
    (ret: seq<uint8>)
    ensures
      if |ec| == 0 then
      // These all deal with |ec| == 0

      //= compliance/data-format/message-header.txt#2.5.1.7.1
      //= type=implication
      //# When the encryption context (../framework/structures.md#encryption-
      //# context) is empty, the value of this field MUST be 0.

      //= compliance/data-format/message-header.txt#2.5.1.7.2
      //= type=implication
      //# When the encryption
      //# context (../framework/structures.md#encryption-context) is empty,
      //# this field MUST NOT be included in the Section 2.5.1.7.

      ret == WriteUint16(|ec| as uint16)
    else
      //= compliance/data-format/message-header.txt#2.5.1.7.2.1
      //= type=implication
      //# The value of this field MUST be greater
      //# than 0.
      && var aad := WriteAAD(ec);
      && ret == WriteUint16(|aad| as uint16) + aad
    {
    if |ec| == 0 then WriteUint16(0)
    else
      var aad := WriteAAD(ec);
      WriteUint16(|aad| as uint16) + aad
  }

  //= compliance/data-format/message-header.txt#2.5.1.7.2
  //#The following table describes the fields that form the Key Value
  //#Pairs.  The bytes are appended in the order shown.
  //#
  //#  +==================+=========================+==================+
  //#  | Field            | Length (bytes)          | Interpreted as   |
  //#  +==================+=========================+==================+
  //#  | Key Value Pair   | 2                       | UInt16           |
  //#  | Count (Section   |                         |                  |
  //#  | 2.5.1.7.2.1)     |                         |                  |
  //#  +------------------+-------------------------+------------------+
  //#  | Key Value Pair   | Variable.  Determined   | Key Value Pair   |
  //#  | Entries (Section | by the count and length | Entries (Section |
  //#  | 2.5.1.7.2.2)     | of each key-value pair. | 2.5.1.7.2.2)     |
  //#  +------------------+-------------------------+------------------+
  function method WriteAAD(
    ec: ESDKCanonicalEncryptionContext
  ):
    (ret: seq<uint8>)
    ensures HasUint16Len(ret)
    // To support older versions of the ESDK
    // |ec| == 0 is encoded as 0 count.
    // However, this is never called on write path.
    // See WriteAADSection
    ensures |ec| == 0 ==> ret == WriteUint16(0)
  {
    WriteUint16(|ec| as uint16) + WriteAADPairs(ec)
  }

  function method {:tailrecursion} WriteAADPairs(
    ec: ESDKCanonicalEncryptionContext
  ):
    (ret: seq<uint8>)
    ensures |ec| == 0
    ==>
      && LinearLength(ec) == |ret|
      && ret == []
    ensures |ec| != 0
    ==>
      && LinearLength(Seq.DropLast(ec)) + PairLength(Seq.Last(ec)) == |ret|
      && WriteAADPairs(Seq.DropLast(ec)) + WriteAADPair(Seq.Last(ec)) == ret
    ensures |ret| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
  {
    if |ec| == 0 then []
    else
      assert LinearLength(Seq.DropLast(ec)) < LinearLength(ec);
      WriteAADPairs(Seq.DropLast(ec)) + WriteAADPair(Seq.Last(ec))
  }

  //= compliance/data-format/message-header.txt#2.5.1.7.2.2
  //# The following table describes the fields that form each key value
  //# pair entry.  The bytes are appended in the order shown.
  //#
  //# +========+=========================================+================+
  //# | Field  | Length (bytes)                          | Interpreted    |
  //# |        |                                         | as             |
  //# +========+=========================================+================+
  //# | Key    | 2                                       | UInt16         |
  //# | Length |                                         |                |
  //# +--------+-----------------------------------------+----------------+
  //# | Key    | Variable.  Equal to the value specified | UTF-8 encoded  |
  //# |        | in the previous 2 bytes (Key Length).   | bytes          |
  //# +--------+-----------------------------------------+----------------+
  //# | Value  | 2                                       | UInt16         |
  //# | Length |                                         |                |
  //# +--------+-----------------------------------------+----------------+
  //# | Value  | Variable.  Equal to the value specified | UTF-8 encoded  |
  //# |        | in the previous 2 bytes (Value Length). | bytes          |
  //# +--------+-----------------------------------------+----------------+
  function method WriteAADPair(
    pair: ESDKEncryptionContextPair
  ):
    (ret: seq<uint8>)
    ensures PairLength(pair) == |ret|
  {
    WriteShortLengthSeq(pair.key) + WriteShortLengthSeq(pair.value)
  }

  function method ReadAADPair(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<ESDKEncryptionContextPair>)
    ensures CorrectlyRead(buffer, res, WriteAADPair)
    ensures res.Success? ==> PairLength(res.value.data) == res.value.tail.start - buffer.start
  {
    var SuccessfulRead(key, keyEnd) :- ReadShortLengthSeq(buffer);
    :- Need(ValidUTF8Seq(key), Error("Invalid Encryption Context key"));
    var SuccessfulRead(value, tail) :- ReadShortLengthSeq(keyEnd);
    :- Need(ValidUTF8Seq(value), Error("Invalid Encryption Context value"));
    var pair:ESDKEncryptionContextPair := Pair(key, value);
    Success(SuccessfulRead(pair, tail))
  }

  function method {:tailrecursion} ReadAADPairs(
    buffer: ReadableBuffer,
    accumulator: ESDKCanonicalEncryptionContext,
    keys: set<UTF8.ValidUTF8Bytes>,
    count: uint16,
    nextPair: ReadableBuffer
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    requires 0 <= |accumulator| <= count as nat < UINT16_LIMIT
    requires CorrectlyRead(buffer, Success(SuccessfulRead(accumulator, nextPair)), WriteAADPairs)
    requires KeysToSet(accumulator) == keys
    decreases count as int - |accumulator|
    ensures res.Success? ==> count as nat == |res.value.data|
    ensures CorrectlyRead(buffer, res, WriteAADPairs)
  {
    if count as int > |accumulator| then
      var SuccessfulRead(pair, newPos) :- ReadAADPair(nextPair);
      :- Need(pair.key !in keys, Error("Duplicate Encryption Context key value."));
      :- Need(newPos.start - buffer.start < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH, Error("Encryption Context exceeds maximum length."));

      var nextAcc := accumulator + [pair];
      // Calling `KeysToSet` once per pair
      // will be faster than calling it on `nextAcc` every time.
      reveal KeysToSet();
      assert KeysToSet(nextAcc) == keys + KeysToSet([pair]);
      var nextKeys := keys + KeysToSet([pair]);

      assert LinearLength(nextAcc) == LinearLength(accumulator) + PairLength(pair);
      assert KeysAreUnique(nextAcc);

      ReadAADPairs(buffer, nextAcc, nextKeys, count, newPos)
    else
      assert CorrectlyRead(buffer, Success(SuccessfulRead(accumulator, nextPair)), WriteAADPairs);
      Success(SuccessfulRead(accumulator, nextPair))
  }

  function method ReadAAD(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    ensures CorrectlyRead(buffer, res, WriteAAD)
  {
    var SuccessfulRead(count, ecPos) :- ReadUInt16(buffer);
    if count == 0 then
      var edks: ESDKCanonicalEncryptionContext := [];
      assert CorrectlyRead(buffer, Success(SuccessfulRead(edks, ecPos)), WriteAAD);
      Success(SuccessfulRead(edks, ecPos))
    else
      var accumulator := [];
      var keys := KeysToSet(accumulator);
      var SuccessfulRead(pairs, tail) :- ReadAADPairs(ecPos, accumulator, keys, count, ecPos);
      Success(SuccessfulRead(pairs, tail))
  }

  function method {:opaque} ReadAADSection(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    ensures IsExpandedAADSection(buffer)
    ==>
      && res.Success?
      && |res.value.data| == 0
    ensures
      && ReadUInt16(buffer).Success?
      && ReadUInt16(buffer).value.data == 0
    ==>
      && res.Success?
      && |res.value.data| == 0
      // && buffer.start + 2 == res.value.tail.start
    ensures if IsExpandedAADSection(buffer) then
      CorrectlyRead(buffer, res, WriteExpandedAADSection)
    else 
      CorrectlyRead(buffer, res, WriteAADSection)
  {
    var length :- ReadUInt16(buffer);
    if length.data == 0 then
      var empty: ESDKCanonicalEncryptionContext := [];

      assert WriteAADSection(empty) == ReadRange((buffer, length.tail));

      Success(SuccessfulRead(empty, length.tail))
    else
      :- Need(length.tail.start + length.data as nat <= |length.tail.bytes|, MoreNeeded(length.tail.start + length.data as nat));

      var verifyCount :- ReadUInt16(length.tail);
      if length.data == 2 then
        // This is the expanded case referred to in IsStandardCompressedAADSection.
        // It is not a canonically correct message,
        // but it should still be parsed.
        :- Need(verifyCount.data == 0, Error("Encryption Context pairs count can not exceed byte length"));
        var empty: ESDKCanonicalEncryptionContext := [];

        assert WriteExpandedAADSection(empty) == ReadRange((buffer, verifyCount.tail));

        Success(SuccessfulRead(empty, verifyCount.tail))
      else 
        // This count MUST be greater than 0,
        // because the length of the AAD is greater than 2.
        :- Need(0 < verifyCount.data, Error("Encryption Context byte length exceeds pairs count."));

        var aad :- ReadAAD(length.tail);
        :- Need(aad.tail.start - length.tail.start == length.data as nat, Error("AAD Length did not match stored length."));

        assert WriteAADSection(aad.data) <= buffer.bytes[buffer.start..];

        Success(aad)
  }

  function method {:opaque} KeysToSet<K(==), V(==)>(pairs: Linear<K, V>): set<K>
  {
    set p: Pair<K,V> | p in pairs :: p.key
  }

  // Makes sure that the AAD Section is optimally encoded.
  // The AAD section is supposed to encode
  // an empty encryption context, {}, as a length of 0
  // because the additional 2 bytes to encode 0 pairs are redundant.
  // However, since there did once exists ESDKs
  // that incorrectly wrote empty encryption contexts as
  // `[0,2,0,0]` this read path MUST be supported.
  predicate IsExpandedAADSection(
    buffer: ReadableBuffer
  )
  {
    && buffer.start + 2 <= |buffer.bytes|
    && var sectionLength := ReadUInt16(buffer).value;
    && sectionLength.data == 2
    && sectionLength.tail.start + 2 <= |buffer.bytes|
    && ReadUInt16(sectionLength.tail).value.data == 0
  }

  // This is *not* a function method,
  // because it is *only* used for correctness.
  // This represents the sub-optimal encoding of AAD
  // with an extra 2 bytes.
  function WriteExpandedAADSection(
    ec: ESDKCanonicalEncryptionContext
  ):
    (ret: seq<uint8>)
    ensures if |ec| == 0 then
      ret == [0, 2, 0, 0]
    else
      && var aad := WriteAAD(ec);
      && ret == UInt16ToSeq(|aad| as uint16) + aad
    {
    var aad := WriteAAD(ec);
    UInt16ToSeq(|aad| as uint16) + aad
  }

  // Completeness Lemmas to prove that ReadX/WriteX are both sound and complete


  // This lemma is to prove that a buffer with bytes from `WriteAADPair`
  // MUST be `ReadAADPair` Success?
  lemma ReadAADPairIsComplete(
    data: ESDKEncryptionContextPair,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKEncryptionContextPair>)
    requires
      && WriteAADPair(data) == bytes
      && buffer.start <= |buffer.bytes|
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && ret.tail.bytes == buffer.bytes
      && Success(ret) == ReadAADPair(buffer)
  {
    assert bytes == WriteShortLengthSeq(data.key) + WriteShortLengthSeq(data.value);
    assert bytes[..|WriteShortLengthSeq(data.key)|] == WriteShortLengthSeq(data.key);

    var key := ReadShortLengthSeqIsComplete(data.key, WriteShortLengthSeq(data.key), buffer);
    assert key.data == data.key;

    var value := ReadShortLengthSeqIsComplete(data.value, WriteShortLengthSeq(data.value), key.tail);
    assert value.data == data.value;

    return ReadAADPair(buffer).value;
  }

  // When dealing with a seq<Pairs> that is `ESDKCanonicalEncryptionContext?`
  // we need to be able to break up this single `seq` into parts.
  // This is slightly complicated because the subSeqs
  // MUST still satisfy `ESDKCanonicalEncryptionContext?`.
  // This is true to a human,
  // Dafny complains a little about the uniqueness constraint,
  // but mostly about the length.
  // This is done by breaking up a single seq
  // because the requirements made proof about
  // 2 parts difficult to put back together.
  lemma ESDKCanonicalEncryptionContextCanBeSplit(
    data: ESDKCanonicalEncryptionContext
  )
    ensures forall accumulator
    | accumulator <= data
    ::
      && ESDKCanonicalEncryptionContext?(accumulator)
      && ESDKCanonicalEncryptionContext?(data[|accumulator|..])
  {
    forall accumulator
    | accumulator <= data
    ensures
      && ESDKCanonicalEncryptionContext?(accumulator)
      && ESDKCanonicalEncryptionContext?(data[|accumulator|..])
    {
      assert |accumulator| <= |data|;
      assert |data[|accumulator|..]| <= |data|;
      assert KeysAreUnique(accumulator);
      assert KeysAreUnique(data[|accumulator|..]);
      assert data == accumulator + data[|accumulator|..];
      LinearLengthIsDistributive(accumulator, data[|accumulator|..]);
      // Each part MUST be less than `ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH`
      // Since the whole MUST be less than this does the trick.
      assert LinearLength(data) == LinearLength(accumulator) + LinearLength(data[|accumulator|..]);
    }
  }

  // What it says on the can.
  // Need to be able to reason about subSeq of a given ESDKCanonicalEncryptionContext.
  lemma WriteAADPairsIsDistributive(
    a: ESDKCanonicalEncryptionContext,
    b: ESDKCanonicalEncryptionContext
  )
    requires ESDKCanonicalEncryptionContext?(a + b)
    ensures WriteAADPairs(a + b) == WriteAADPairs(a) + WriteAADPairs(b)
  {
    if b == [] {
      assert a + b == a;
    } else {
      calc {
        WriteAADPairs(a + b);
      == // Definition of WriteAADPairs
        if |a+b| == 0 then []
        else WriteAADPairs(Seq.DropLast(a + b)) + WriteAADPair(Seq.Last(a+b));
      == {assert |a+b| > 0;} // Because of the above `if` block
        WriteAADPairs(Seq.DropLast(a + b)) + WriteAADPair(Seq.Last(a+b));
      == {assert Seq.Last(a+b) == Seq.Last(b) && Seq.DropLast(a+b) == a + Seq.DropLast(b);} // Breaking apart (a+b)
        WriteAADPairs(a + Seq.DropLast(b)) + WriteAADPair(Seq.Last(b));
      == {WriteAADPairsIsDistributive(a, Seq.DropLast(b));} // This lets us break apart WriteAADPairs(a + Seq.DropLast(b))
        (WriteAADPairs(a) + WriteAADPairs(Seq.DropLast(b))) + WriteAADPair(Seq.Last(b));
      == // Move () to prove associativity of +
        WriteAADPairs(a) + (WriteAADPairs(Seq.DropLast(b)) + WriteAADPair(Seq.Last(b)));
      == {assert WriteAADPairs(Seq.DropLast(b)) + WriteAADPair(Seq.Last(b)) == WriteAADPairs(b);} // join the 2 parts of b back together
        WriteAADPairs(a) + WriteAADPairs(b);
      }
    }
  }

  // Proving that a ReadableBuffer
  // satisfies the preconditions for ReadAADPairs
  // is a little complicated.
  // Moving this into a separate lemma
  // simplified `ReadAADPairsIsComplete`.
  lemma NextPairIsComplete(
    data: ESDKCanonicalEncryptionContext,
    accumulator: ESDKCanonicalEncryptionContext,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: ReadableBuffer)
    requires
      && WriteAADPairs(data) == bytes
      && accumulator <= data
      && accumulator != data
      && buffer.start <= |buffer.bytes|
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.bytes == buffer.bytes
      && ret.start == buffer.start + |WriteAADPairs(accumulator)|
      && buffer.start <= ret.start <= |ret.bytes|
      && WriteAADPair(data[|accumulator|]) <= ret.bytes[ret.start..]
  {
    ESDKCanonicalEncryptionContextCanBeSplit(data);

    var nextAccumulator := data[..|accumulator| + 1]; //   accumulator +  [data[|accumulator|]];
    assert 0 <= |accumulator| < |nextAccumulator| <= |data|;
    assert nextAccumulator + data[|nextAccumulator|..] == data;
    assert ESDKCanonicalEncryptionContext?(nextAccumulator);
    assert ESDKCanonicalEncryptionContext?(data[|nextAccumulator|..]);

    // Need to break out `WriteAADPair(data[|accumulator|])`
    // so that the returned buffer has the position
    // provable correct for the "next pair"
    calc {
      bytes;
    == // From requires clause
      WriteAADPairs(data);
    == {WriteAADPairsIsDistributive(nextAccumulator, data[|nextAccumulator|..]);}
      WriteAADPairs(nextAccumulator) + WriteAADPairs(data[|nextAccumulator|..]);
    == {assert WriteAADPairs(Seq.DropLast(nextAccumulator)) + WriteAADPair(Seq.Last(nextAccumulator)) == WriteAADPairs(nextAccumulator);}
      (WriteAADPairs(Seq.DropLast(nextAccumulator)) + WriteAADPair(Seq.Last(nextAccumulator))) + WriteAADPairs(data[|nextAccumulator|..]);
    == {assert Seq.DropLast(nextAccumulator) == accumulator && WriteAADPairs(Seq.DropLast(nextAccumulator)) == WriteAADPairs(accumulator);}
      WriteAADPairs(accumulator) + WriteAADPair(Seq.Last(nextAccumulator)) + WriteAADPairs(data[|nextAccumulator|..]);
    == {assert Seq.Last(nextAccumulator) == data[|accumulator|];}
      WriteAADPairs(accumulator) + WriteAADPair(data[|accumulator|]) + WriteAADPairs(data[|nextAccumulator|..]);
    }

    // This puts `WriteAADPair(data[|accumulator|])` which is what we want!
    assert WriteAADPairs(accumulator) + WriteAADPair(data[|accumulator|]) + WriteAADPairs(data[|nextAccumulator|..]) <= buffer.bytes[buffer.start..];
    assert WriteAADPairs(accumulator) + WriteAADPair(data[|accumulator|]) <= buffer.bytes[buffer.start..];
    assert WriteAADPairs(accumulator) <= buffer.bytes[buffer.start..];

    return buffer.( start := buffer.start + |WriteAADPairs(accumulator)| );
  }

  lemma {:vcs_split_on_every_assert} ReadAADPairsIsComplete(
    data: ESDKCanonicalEncryptionContext,
    accumulator: ESDKCanonicalEncryptionContext,
    keys: set<UTF8.ValidUTF8Bytes>,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKCanonicalEncryptionContext>)
    decreases |data| - |accumulator|

    requires accumulator <= data
    requires KeysToSet(accumulator) == keys

    requires
      && WriteAADPairs(data) == bytes
      && buffer.start <= |buffer.bytes|
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && ret.tail.bytes == buffer.bytes

      && var nextPair := buffer.(start := buffer.start + |WriteAADPairs(accumulator)|);
      && nextPair.bytes == buffer.bytes
      && WriteAADPairs(accumulator) <= bytes

      && Success(ret) == ReadAADPairs(buffer, accumulator, keys, |data| as uint16, nextPair)
  {
    var keys := KeysToSet(accumulator);

    // This will match _both_ the case where |data| == 0 && the terminal case.
    // It is expressed this way because we are,
    // building up to the terminal case (see the inductive call below)
    if data == accumulator {
      return ReadAADPairs(
        buffer,
        accumulator,
        keys,
        |data| as uint16,
        buffer.( start := buffer.start + |WriteAADPairs(data)| ))
      .value;
    } else {

      assert accumulator < data;

      var nextPair := NextPairIsComplete(data, accumulator, bytes, buffer);
      assert WriteAADPair(data[|accumulator|]) <= nextPair.bytes[nextPair.start..];

      // Since we know that the bytes here at `nextPair`
      // are valid WriteAADPair bytes,
      // we can prove that this part is complete
      var pair := ReadAADPairIsComplete(
        data[|accumulator|],
        WriteAADPair(data[|accumulator|]),
        nextPair
      );

      assert pair.data == data[|accumulator|];
      reveal KeysToSet();
      assert pair.data.key !in keys;
      assert pair.data in data;
      assert accumulator + [pair.data] <= data;

      // The length constraint is a little complicated.
      // Dafny wants to know the length of bytes is in bounds.
      // This is obviously true,
      // because Dafny believes that the `|bytes| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH`.
      // Dafny also believes that `LinearLength(accumulator) < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH`.
      // Adding `[pair.data]` to accumulator is the part that it is unsure about.
      LinearLengthIsDistributive(accumulator + [pair.data], data[|(accumulator + [pair.data])|..]);
      assert accumulator + [pair.data] + data[|(accumulator + [pair.data])|..] == data;
      assert LinearLength(accumulator + [pair.data]) + LinearLength(data[|(accumulator + [pair.data])|..]) == LinearLength(data);
      assert LinearLength(accumulator + [pair.data]) <= LinearLength(data);
      assert pair.tail.start - buffer.start < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH;

      assert KeysToSet(accumulator + [pair.data]) == keys + KeysToSet([pair.data]);

      // Invoking the inductive hypothesis
      // This will recurse *forward* to the final case where data == accumulator.
      // Along the way, we prove ReadAADPairIsComplete
      // for each encryption context pair "along the way".
      ret := ReadAADPairsIsComplete(
        data,
        accumulator + [pair.data],
        keys + KeysToSet([pair.data]),
        bytes,
        buffer
      );
    }
  }

  lemma ReadAADIsComplete(
    data: ESDKCanonicalEncryptionContext,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKCanonicalEncryptionContext>)
    requires
      && WriteAAD(data) == bytes
      && buffer.start <= |buffer.bytes|
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && ret.tail.bytes == buffer.bytes
      && Success(ret) == ReadAAD(buffer)
  {

    assert WriteUint16(|data| as uint16) + WriteAADPairs(data) == bytes;
    assert bytes[|WriteUint16(|data| as uint16)|..] == WriteAADPairs(data);

    var count := ReadUInt16IsComplete(
      |data| as uint16,
      WriteUint16(|data| as uint16),
      buffer
    );
    assert count.data as nat == |data|;
    var accumulator:ESDKCanonicalEncryptionContext := [];

    var pairs := ReadAADPairsIsComplete(
      data,
      accumulator,
      KeysToSet(accumulator),
      WriteAADPairs(data),
      count.tail
    );
    assert pairs.data == data;

    return ReadAAD(buffer).value;
  }

  lemma ReadAADSectionIsComplete(
    data: ESDKCanonicalEncryptionContext,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKCanonicalEncryptionContext>)
    requires
      && WriteAADSection(data) == bytes
      && buffer.start <= |buffer.bytes|
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && ret.tail.bytes == buffer.bytes
      && Success(ret) == ReadAADSection(buffer)
  {
    reveal ReadAADSection();
    assert 2 <= |bytes|;
    assert |data| == 0 ==> WriteAADSection(data) == WriteUint16(0);

    if 0 == |data| {
      assert ReadUInt16(buffer).value.data == 0;
      return ReadAADSection(buffer).value;
    } else {
      assert WriteUint16(|WriteAAD(data)| as uint16) + WriteAAD(data) == bytes;
      assert 0 < |data|;

      var length := ReadUInt16IsComplete(
        |WriteAAD(data)| as uint16,
        WriteUint16(|WriteAAD(data)| as uint16),
        buffer
      );
      assert length.data == |WriteAAD(data)| as uint16;
      assert length.tail.start + length.data as nat <= |length.tail.bytes|;
      assert !IsExpandedAADSection(buffer);

      var aad := ReadAADIsComplete(
        data,
        WriteAAD(data),
        length.tail
      );
      assert aad.data == data;

      return ReadAADSection(buffer).value;
    }
  }
}
