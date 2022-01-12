// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "../../Util/Sets.dfy"

module EncryptionContext {
  import Aws.Crypto
  import Seq
  import StandardLibrary
  import Sets
  import opened SerializableTypes
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
  |
    && HasUint16Len(pairs)
    && LinearLength(pairs) < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
    //= compliance/data-format/message-header.txt#2.5.1.7.2.2
    //= type=implication
    //# This sequence MUST NOT contain duplicate entries.
    && KeysAreUnique(pairs)
  witness *

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
    :(ret: Crypto.EncryptionContext)
    ensures |canonicalEncryptionContext| == 0 ==> |ret| == 0
  {
    // This is needed because Dafny can not reveal the subset type by default?
    assert KeysAreUnique(canonicalEncryptionContext);
    map i
    | 0 <= i < |canonicalEncryptionContext|
    :: canonicalEncryptionContext[i].key := canonicalEncryptionContext[i].value
  }

  lemma LemmaCardinalityOfEncryptionContextEqualsPairs(
    pairs: ESDKCanonicalEncryptionContext,
    ec: Crypto.EncryptionContext
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

  lemma {:vcs_split_on_every_assert} LemmaLengthOfPairsEqualsEncryptionContext(
    pairs: ESDKCanonicalEncryptionContext,
    ec: Crypto.EncryptionContext
  )
    requires ec == GetEncryptionContext(pairs)
    ensures LinearLength(pairs) == Length(ec)
  {
    if |pairs| == 0 {
    } else {
      // assert {:split_here} true;
      var front := Seq.DropLast(pairs);
      var tail := Seq.Last(pairs);
      var ecOfFront := GetEncryptionContext(front);

      assert pairs == front + [tail];
      // assert {:split_here} true;
      assert ec.Keys == ecOfFront.Keys + {tail.key};
      assert ec == ecOfFront + map[tail.key := tail.value];
      assert |ecOfFront.Keys| == |ecOfFront|;

      // assert {:split_here} true;
      assert LinearLength(pairs) == Length(ec);

      // assert {:split_here} true;
      LemmaLengthOfPairsEqualsEncryptionContext(front, ecOfFront);
    }

  }

  lemma LemmaESDKCanonicalEncryptionContextIsESDKEncryptionContext(
    pairs: ESDKCanonicalEncryptionContext,
    ec: Crypto.EncryptionContext
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

      ret == [0, 0]
    else
      //= compliance/data-format/message-header.txt#2.5.1.7.2.1
      //= type=implication
      //# The value of this field MUST be greater
      //# than 0.
      && var aad := WriteAAD(ec);
      && ret == UInt16ToSeq(|aad| as uint16) + aad
    {
    if |ec| == 0 then UInt16ToSeq(0)
    else
      var aad := WriteAAD(ec);
      UInt16ToSeq(|aad| as uint16) + aad
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
    ensures |ec| == 0 ==> ret == UInt16ToSeq(0)
  {
    UInt16ToSeq(|ec| as uint16) + WriteAADPairs(ec)
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
    ensures res.Success?
    ==>
       && count as nat == |res.value.data|
    ensures CorrectlyRead(buffer, res, WriteAADPairs)
  {
    if count as int > |accumulator| then
      var SuccessfulRead(pair, newPos) :- ReadAADPair(nextPair);
      :- Need(pair.key !in keys, Error("Duplicate Encryption Context key value."));
      :- Need(|newPos.bytes[buffer.start..newPos.start]| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH, Error("Encryption Context exceeds maximum length."));

      var nextAcc := accumulator + [pair];
      // Calling `KeysToSet` once per pair
      // will be faster than calling it on `nextAcc` every time.
      reveal KeysToSet();
      assert KeysToSet(nextAcc) == keys + KeysToSet([pair]);
      var nextKeys := keys + KeysToSet([pair]);

      assert LinearLength(nextAcc) == LinearLength(accumulator) + PairLength(pair);
      assert KeysAreUnique(nextAcc);

      ghost var why? := [buffer, nextPair, newPos];
      assert {:split_here} true;
      ConsecutiveReadsAreAssociative(why?);

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

  function method ReadAADSection(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
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

        assert WriteAADSection(aad.data) == ReadRange((buffer, aad.tail));

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
    && buffer.start + |[0, 2]| <= |buffer.bytes|
    && ReadRange((buffer, MoveStart(buffer, |[0, 2]|))) == [0, 2]
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
}
