// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"

module EncryptedDataKeys {
  import Aws.Crypto
  import Seq
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  function method WriteEncryptedDataKey(edk: ESDKEncryptedDataKey): (ret: seq<uint8>)
  {
    WriteShortLengthSeq(edk.keyProviderId)
    + WriteShortLengthSeq(edk.keyProviderInfo)
    + WriteShortLengthSeq(edk.ciphertext)
  }

  function method {:tailrecursion} WriteEncryptedDataKeys(
    edks: ESDKEncryptedDataKeys
  ):
    (ret: seq<uint8>)
  {
    if |edks| == 0 then []
    else
      WriteEncryptedDataKeys(Seq.DropLast(edks)) + WriteEncryptedDataKey(Seq.Last(edks))
  }

  function method WriteEncryptedDataKeysSection(
    edks: ESDKEncryptedDataKeys
  ):
    (ret: seq<uint8>)
  {
    UInt16ToSeq(|edks| as uint16) + WriteEncryptedDataKeys(edks)
  }

  function method ReadEncryptedDataKey(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<ESDKEncryptedDataKey>)
    ensures CorrectlyRead(buffer, res, WriteEncryptedDataKey)
  {
    var SuccessfulRead(providerId, providerIdPos) :- ReadShortLengthSeq(buffer);
    :- Need(ValidUTF8Seq(providerId), Error("Invalid providerID"));
    var SuccessfulRead(providerInfo, providerInfoPos) :- ReadShortLengthSeq(providerIdPos);
    var SuccessfulRead(cipherText, tail) :- ReadShortLengthSeq(providerInfoPos);
    var edk: ESDKEncryptedDataKey := Crypto.EncryptedDataKey(
        keyProviderId := providerId,
        keyProviderInfo := providerInfo,
        ciphertext := cipherText);

    Success(SuccessfulRead(edk, tail))
  }

  function method {:tailrecursion true} ReadEncryptedDataKeys(
    buffer: ReadableBuffer,
    accumulator: ESDKEncryptedDataKeys,
    count: uint16,
    nextEdkStart: ReadableBuffer
  )
    :(res: ReadCorrect<ESDKEncryptedDataKeys>)
    requires 0 <= |accumulator| <= count as nat < UINT16_LIMIT
    requires CorrectlyRead(buffer, Success(SuccessfulRead(accumulator, nextEdkStart)), WriteEncryptedDataKeys)
    decreases count as int - |accumulator|
    ensures CorrectlyRead(buffer, res, WriteEncryptedDataKeys)
    ensures res.Success? ==> count as nat == |res.value.data|
  {
    if count as int > |accumulator| then
      var SuccessfulRead(edk, newPos) :- ReadEncryptedDataKey(nextEdkStart);
      var nextAcc := accumulator + [edk];
      ReadEncryptedDataKeys(buffer, nextAcc, count, newPos)
    else
      Success(SuccessfulRead(accumulator, nextEdkStart))
  }

  function method {:opaque} ReadEncryptedDataKeysSection(
    buffer: ReadableBuffer,
    maxEdks: Option<int64>
  )
    :(res: ReadCorrect<ESDKEncryptedDataKeys>)
    ensures CorrectlyRead(buffer, res, WriteEncryptedDataKeysSection)
  {
    var SuccessfulRead(count, edkStart) :- ReadUInt16(buffer);
    
    if
      && maxEdks.Some?
      && maxEdks.value > 0 // TODO: remove once CrypTool-4350 fixed
      && count as int64 > maxEdks.value
    then
      //= compliance/client-apis/decrypt.txt#2.7.1
      //# If the number of encrypted data keys (../framework/
      //# structures.md#encrypted-data-keys) deserialized from the message
      //# header (../data-format/message-header.md) is greater than the maximum
      //# number of encrypted data keys (client.md#maximum-number-of-encrypted-
      //# data-keys) configured in the client (client.md), then as soon as that
      //# can be determined during deserializing decrypt MUST process no more
      //# bytes and yield an error.
      Failure(Error("Ciphertext encrypted data keys exceed maxEncryptedDataKeys"))
    else
      var SuccessfulRead(edks, tail) :- ReadEncryptedDataKeys(edkStart, [], count, edkStart);
      Success(SuccessfulRead(edks, tail))
  }

  // Completeness Lemmas to prove that ReadX/WriteX are both sound and complete

  lemma ReadEncryptedDataKeyIsComplete(
    data: ESDKEncryptedDataKey,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKEncryptedDataKey>)
    requires
      && WriteEncryptedDataKey(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadEncryptedDataKey(buffer)
  {
    assert bytes
    == WriteShortLengthSeq(data.keyProviderId)
    + WriteShortLengthSeq(data.keyProviderInfo)
    + WriteShortLengthSeq(data.ciphertext);

    assert WriteShortLengthSeq(data.keyProviderId) <= bytes;
    assert WriteShortLengthSeq(data.keyProviderInfo) <= bytes[|WriteShortLengthSeq(data.keyProviderId)|..];
    assert WriteShortLengthSeq(data.ciphertext) == bytes[|WriteShortLengthSeq(data.keyProviderId) + WriteShortLengthSeq(data.keyProviderInfo)|..];

    var keyProviderId := ReadShortLengthSeqIsComplete(data.keyProviderId, WriteShortLengthSeq(data.keyProviderId), buffer);
    assert keyProviderId.data == data.keyProviderId;

    var keyProviderInfo := ReadShortLengthSeqIsComplete(data.keyProviderInfo, WriteShortLengthSeq(data.keyProviderInfo), keyProviderId.tail);
    assert keyProviderInfo.data == data.keyProviderInfo;

    var ciphertext := ReadShortLengthSeqIsComplete(data.ciphertext, WriteShortLengthSeq(data.ciphertext), keyProviderInfo.tail);
    assert ciphertext.data == data.ciphertext;

    return ReadEncryptedDataKey(buffer).value;
  }

  // This lemma turned out to be less useful
  // but it is super helpful as documentation about how to use `calc`
  lemma WriteEncryptedDataKeysIsDistributive(
    a: ESDKEncryptedDataKeys,
    b: ESDKEncryptedDataKeys
  )
    requires HasUint16Len(a + b)
    ensures WriteEncryptedDataKeys(a + b) == WriteEncryptedDataKeys(a) + WriteEncryptedDataKeys(b)
  {
    if b == [] {
      assert a + b == a;
    } else {
      calc {
        WriteEncryptedDataKeys(a + b);
      == // Definition of WriteEncryptedDataKeys
        if |a+b| == 0 then []
        else WriteEncryptedDataKeys(Seq.DropLast(a + b)) + WriteEncryptedDataKey(Seq.Last(a+b));
      == {assert |a+b| > 0;} // Because of the above `if` block
        WriteEncryptedDataKeys(Seq.DropLast(a + b)) + WriteEncryptedDataKey(Seq.Last(a+b));
      == {assert Seq.Last(a+b) == Seq.Last(b) && Seq.DropLast(a+b) == a + Seq.DropLast(b);} // Breaking apart (a+b)
        WriteEncryptedDataKeys(a + Seq.DropLast(b)) + WriteEncryptedDataKey(Seq.Last(b));
      == {WriteEncryptedDataKeysIsDistributive(a, Seq.DropLast(b));} // This lets us break apart WriteEncryptedDataKeys(a + Seq.DropLast(b))
        (WriteEncryptedDataKeys(a) + WriteEncryptedDataKeys(Seq.DropLast(b))) + WriteEncryptedDataKey(Seq.Last(b));
      == // Move () to prove associativity of +
        WriteEncryptedDataKeys(a) + (WriteEncryptedDataKeys(Seq.DropLast(b)) + WriteEncryptedDataKey(Seq.Last(b)));
      == {assert WriteEncryptedDataKeys(Seq.DropLast(b)) + WriteEncryptedDataKey(Seq.Last(b)) == WriteEncryptedDataKeys(b);} // join the 2 parts of b back together
        WriteEncryptedDataKeys(a) + WriteEncryptedDataKeys(b);
      }
    }
  }

  lemma ReadEncryptedDataKeysIsComplete(
    data: ESDKEncryptedDataKeys,
    accumulator: ESDKEncryptedDataKeys,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<ESDKEncryptedDataKeys>)
    decreases |data| - |accumulator|
    requires
      && WriteEncryptedDataKeys(data) == bytes
      && accumulator <= data
      && buffer.start + |bytes| <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.bytes == buffer.bytes
      && ret.tail.start == buffer.start + |bytes|

      && var nextEdkStart := buffer.(start := buffer.start + |WriteEncryptedDataKeys(accumulator)|);
      && nextEdkStart.bytes == buffer.bytes
      && WriteEncryptedDataKeys(accumulator) <= bytes

      && Success(ret) == ReadEncryptedDataKeys(buffer, accumulator, |data| as uint16, nextEdkStart)
  {
    var nextEdkStart := buffer.(start := buffer.start + |WriteEncryptedDataKeys(accumulator)|);
    assert nextEdkStart.bytes == buffer.bytes;

    // This will match _both_ the case where |data| == 0 && the terminal case.
    // It is expressed this way because we are,
    // building up to the terminal case (see the inductive call below)
    if data == accumulator {
      return ReadEncryptedDataKeys(buffer, accumulator, |data| as uint16, nextEdkStart).value;
    } else {
      // WriteEncryptedDataKeys is defined as WriteEncryptedDataKeys(DropLast) + WriteEncryptedDataKey(Last)
      // This means that we can easily prove n-1 and n,
      // because n-1 ~ DropLast and n == Last.
      // However, all we know is accumulator <= data.
      // We may be at the very last element or somewhere in the middle.
      // But, because |data| != 0 && we can not be at the end (data == accumulator),
      // then data[|accumulator|] is always a valid index!
      var nextAccumulator := accumulator + [data[|accumulator|]];
      assert data == nextAccumulator + data[|nextAccumulator|..];
      WriteEncryptedDataKeysIsDistributive(nextAccumulator, data[|nextAccumulator|..]);
      assert WriteEncryptedDataKeys(nextAccumulator) <= bytes;
      // This is because WriteEncryptedDataKeys(nextAccumulator) == WriteEncryptedDataKeys(DropLast) + WriteEncryptedDataKey(Last)
      assert WriteEncryptedDataKey(Seq.Last(nextAccumulator)) <= nextEdkStart.bytes[nextEdkStart.start..];

      // Since we know that the bytes here at `nextEdkStart`
      // are valid WriteEncryptedDataKey bytes,
      // we can prove that this part is complete
      var edk := ReadEncryptedDataKeyIsComplete(
        data[|accumulator|],
        WriteEncryptedDataKey(data[|accumulator|]),
        nextEdkStart
      );

      assert edk.data == data[|accumulator|];

      // Invoking the inductive hypothesis
      // This will recurse *forward* to the final case where data == accumulator.
      // Along the way, we prove ReadEncryptedDataKeyIsComplete
      // for each encrypted data key "along the way".
      var edks := ReadEncryptedDataKeysIsComplete(
        data,
        nextAccumulator,
        bytes,
        buffer
      );

      assert edks.data == data;
      assert edks.tail.start == buffer.start + |WriteEncryptedDataKeys(data)|;

      assert {:split_here} true;
      return ReadEncryptedDataKeys(buffer, accumulator, |data| as uint16, nextEdkStart).value;
    }
  }

  lemma ReadEncryptedDataKeysSectionIsComplete(
    data: ESDKEncryptedDataKeys,
    bytes: seq<uint8>,
    buffer: ReadableBuffer,
    maxEdks: Option<int64>
  )
    returns (ret: ReadCorrect<ESDKEncryptedDataKeys>)
    requires
      && WriteEncryptedDataKeysSection(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures ret.Success?
    ==>
      && ret.value.data == data
      && ret.value.tail.start == buffer.start + |bytes|
      && Success(ret.value) == ReadEncryptedDataKeysSection(buffer, maxEdks)
  {
    reveal ReadEncryptedDataKeysSection();
    assert bytes == WriteUint16(|data| as uint16) + WriteEncryptedDataKeys(data);
    assert bytes[|WriteUint16(|data| as uint16)|..] == WriteEncryptedDataKeys(data);

    var count := ReadUInt16IsComplete(
      |data| as uint16,
      WriteUint16(|data| as uint16),
      buffer
    );
    assert count.data == |data| as uint16;

    var edks := ReadEncryptedDataKeysIsComplete(data, [], WriteEncryptedDataKeys(data), count.tail);
    assert edks.data == data;

    var edksSection := ReadEncryptedDataKeysSection(buffer, maxEdks);
    if
      && maxEdks.Some?
      && maxEdks.value > 0 // TODO: remove once CrypTool-4350 fixed
      && |edks.data| as int64 > maxEdks.value
    {
      assert edksSection.Failure?;
      return edksSection;
    } else {
      assert edksSection.Success?;
      return edksSection;
    }
  }

}
