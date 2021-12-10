// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "../../Util/Sets.dfy"

module EncryptionContext2 {
  import Aws.Crypto
  import Seq
  import StandardLibrary
  import Sets
  // import opened SerializableTypes
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

  datatype Pair<K, V> = Pair(key: K, value: V)
  type Linear<K, V> = seq<Pair<K,V>>

  type ESDKEncryptionContextPair = p: Pair<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  |
    && HasUint16Len(p.key) && ValidUTF8Seq(p.key)
    && HasUint16Len(p.value) && ValidUTF8Seq(p.value)
  witness *

  const ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH := UINT16_LIMIT - 2;
  type SeqEcMaxBytes = s: seq<uint8>
  | |s| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
  witness *

  type ESDKCanonicalEncryptionContext = pairs: seq<ESDKEncryptionContextPair>
  |
    && HasUint16Len(pairs)
    && LinearLength2(pairs) < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
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

  function method {:vcs_split_on_every_assert} CanonicalEncryptionContext(
    encryptionContext: ESDKEncryptionContext
  )
    :(ret: ESDKCanonicalEncryptionContext)
  {
    //= compliance/data-format/message-header.txt#2.5.1.7.2.2
    //# These entries MUST have entries sorted, by key, in ascending order
    //# according to the UTF-8 encoded binary value.
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence<uint8>(
      encryptionContext.Keys,
      UInt.UInt8Less
    );
    seq(
      |keys|,
      i
        requires 0 <= i < |keys|
      => Pair(
        keys[i],
        encryptionContext[keys[i]]))
  }

  function method EncryptionContext(
    canonicalEncryptionContext: ESDKCanonicalEncryptionContext
  )
    :(ret: Crypto.EncryptionContext)
  {
    // This is needed because Dafny can not reveal the subset type by default?
    assert KeysAreUnique(canonicalEncryptionContext);
    map p: ESDKEncryptionContextPair
    | p in canonicalEncryptionContext
    :: p.key := p.value
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
    ensures |ec| == 0
    ==>
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

      //= compliance/data-format/message-header.txt#2.5.1.7.2.1
      //= type=implication
      //# The value of this field MUST be greater
      //# than 0.
      ret == UInt16ToSeq(0)
    ensures |ec| != 0
    ==>
      && ret == UInt16ToSeq(|WriteAAD(ec)| as uint16)
        + WriteAAD(ec)
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
    if |ec| == 0 then UInt16ToSeq(0)
    else 
      UInt16ToSeq(|ec| as uint16) + WriteAADPairs(ec)
  }

  function method {:tailrecursion} WriteAADPairs(
    ec: ESDKCanonicalEncryptionContext
  ):
    (ret: seq<uint8>)
    ensures |ec| == 0
    ==>
      && LinearLength2(ec) == |ret|
      && ret == []
    ensures |ec| != 0
    ==>
      && LinearLength2(Seq.DropLast(ec)) + PairLength(Seq.Last(ec)) == |ret|
      && WriteAADPairs(Seq.DropLast(ec)) + WriteAADPair(Seq.Last(ec)) == ret
    ensures |ret| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH
  {
    if |ec| == 0 then []
    else
      assert LinearLength2(Seq.DropLast(ec)) < LinearLength2(ec);
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
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<ESDKEncryptionContextPair>)
    ensures CorrectlyRead(s, pos, res, WriteAADPair)
  {
    var (key, keyEnd) :- ReadShortLengthSeq(s, pos);
    :- Need(ValidUTF8Seq(key), Error("Invalid Encryption Context key"));
    var (value, end) :- ReadShortLengthSeq(s, keyEnd);
    :- Need(ValidUTF8Seq(value), Error("Invalid Encryption Context value"));
    Success((Pair(key, value), end))
  }

  function method {:tailrecursion} ReadAADPairs(
    s: seq<uint8>,
    pos: nat,
    acc: ESDKCanonicalEncryptionContext,
    keys: set<UTF8.ValidUTF8Bytes>,
    count: uint16,
    nextPair: nat
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    requires 0 <= |acc| <= count as nat < UINT16_LIMIT
    requires |s| >= nextPair >= pos
    requires WriteAADPairs(acc) == s[pos..nextPair]
    requires KeysToSet(acc) == keys
    decreases count as int - |acc|
    ensures res.Success?
    ==>
       && count as nat == |res.value.0|
    ensures CorrectlyRead(s, pos, res, WriteAADPairs)
  {
    if count as int > |acc| then
      var (pair, newPos) :- ReadAADPair(s, nextPair);
      :- Need(pair.key !in keys, Error("Duplicate Encryption Context key value."));
      :- Need(|s[pos..newPos]| < ESDK_CANONICAL_ENCRYPTION_CONTEXT_MAX_LENGTH, Error("Encryption Context exceeds maximum length."));

      var nextAcc := acc + [pair];
      var nextKeys := KeysToSet(nextAcc);
      reveal KeysToSet();
      assert KeysToSet(nextAcc) == KeysToSet(acc) + KeysToSet([pair]);
      ReadAADPairs(s, pos, nextAcc, nextKeys, count, newPos)
    else
      assert WriteAADPairs(acc) == s[pos..nextPair];
      Success((acc, nextPair))
  }

  function method ReadAAD(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    ensures CorrectlyRead(s, pos, res, WriteAAD)
  {
    var (count, ecPos) :- ReadUInt16(s, pos);
    if count == 0 then
      var edks: ESDKCanonicalEncryptionContext := [];
      Success((edks, ecPos))
    else
      var acc := [];
      var keys := KeysToSet(acc);
      ReadAADPairs(s, ecPos, acc, keys, count, ecPos)
  }

  function method ReadAADSection(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<ESDKCanonicalEncryptionContext>)
    ensures
      || CorrectlyRead(s, pos, res, WriteAADSection)
      // This is an exceedingly rare case.
      // The AAD section is supposed to encode
      // an empty encryption context as a length of 0
      // because the additional 2 bytes to encode 0 is redundant.
      // However, since there did once exists ESDKs
      // that incorrectly wrote empty encryption contexts as
      // `[0,2,0,0]` this read path MUST be supported.
      || (
        && res.Success?
        && pos+4 < |s|
        && s[pos..pos+4] == [0,2,0,0]
        ==>
          && |res.value.0| == 0
          && res.value.1 == pos + 4)
  {
    var (length: uint16, countPos: nat) :- ReadUInt16(s, pos);
    if length == 0 then
      Success(([], countPos))
    else if countPos + length as nat < |s| then
      Failure(MoreNeeded(countPos + length as nat))
    else if length == 2 then
      var (count, end) :- ReadUInt16(s, countPos);
      :- Need(count == 0, Error("Encryption Context pairs count can not exceed byte length"));
      Success(([], end))
    else
      var (count, _) :- ReadUInt16(s, countPos);
      :- Need(count > 0, Error("Encryption Context byte length exceeds pairs count."));
      ReadAAD(s, countPos)
  }

  function method {:opaque} KeysToSet<K(==), V(==)>(pairs: Linear<K, V>): set<K>
  {
    set p: Pair<K,V> | p in pairs :: p.key
  }



  // Copied from Serialized Types...

  predicate method IsESDKEncryptionContext(ec: Crypto.EncryptionContext) {
    && |ec| < UINT16_LIMIT
    && Length2(ec) < UINT16_LIMIT
    && forall element
    | element in (multiset(ec.Keys) + multiset(ec.Values))
    ::
      && HasUint16Len(element)
      && ValidUTF8Seq(element)
  }

  type ESDKEncryptionContext = ec: Crypto.EncryptionContext | IsESDKEncryptionContext(ec) witness *

  function method Length2(encryptionContext: Crypto.EncryptionContext): nat
  {
    if |encryptionContext| == 0 then 0 else
      // Defining and reasoning about order at this level is simplified by using a sequence of
      // key value pairs instead of a map.
      var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
      var pairs := seq(|keys|, i requires 0 <= i < |keys| => Pair(keys[i], encryptionContext[keys[i]]));
      2 + LinearLength2(pairs)
  }

  function method LinearLength2(
    pairs: Linear<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  ):
    (ret: nat)
    ensures |pairs| == 0 ==> ret == 0
  {
    if |pairs| == 0 then 0
    else
      LinearLength2(Seq.DropLast(pairs)) + PairLength(Seq.Last(pairs))
  }

  function method PairLength(
    pair: Pair<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  ):
    (ret: nat)
  {
    2 + |pair.key| + 2 + |pair.value|
  }

}
