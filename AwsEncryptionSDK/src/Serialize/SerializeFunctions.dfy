// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsEncryptionSdkTypes.dfy"

module SerializeFunctions {
  import Seq
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8

  datatype ReadProblems =
    // This _may_ be recoverable.
    // if these is more data to read,
    // then after getting this data
    // a read function _may_ be able to return a datatype.
    // If the caller is at EOS,
    // then this is not recoverable.
    | MoreNeeded(pos: nat)
    // These errors should not be recoverable.
    // The data is incorrect
    // and reading the same data again will generate the same error.
    | Error(message: string)
  type MoreNeeded = p: ReadProblems | p.MoreNeeded? witness *

  // When reading a buffer,
  // there are the bytes to read,
  // and the position to start reading withing these bytes.
  // This data structure represents this information.
  datatype ReadableBuffer = ReadableBuffer(
    bytes: seq<uint8>,
    start: nat
  )

  // This holds the data from a successful read.
  // The `data` is the read type,
  // and the `tail` is the remaining data left to be read.
  datatype SuccessfulRead<T> = SuccessfulRead(
    data: T,
    tail: ReadableBuffer
  )

  type ReadResult<T, E> = Result<SuccessfulRead<T>, E>
  type ReadCorrect<T> = ReadResult<T, ReadProblems>
  // When reading binary it can not be incorrect.
  // It may not be enough data, but since it is raw binary,
  // it can not be wrong.
  // Generally this T is `seq<uint8>`,
  // but in the a few cases like uint16, uint32, uint64
  // it may be other types.
  type ReadBinaryCorrect<T> = ReadResult<T, MoreNeeded>

  // This is the composable unit
  // that all `ReadX` functions use to prove correctness. 
  // The idea is that WriteX(ReadX(ReadableBuffer)) == ReadableBuffer.
  // That a read is the inverse of a write.
  // The assertion is that the write side is correct _by construction_.
  // This means that the order of writes *is* the correct order,
  // and no additional Dafny specifications are need to define a correct write.
  // This puts the correctness on the write side,
  // and the read side is correct _because_
  // what was read is what would have been written.
  predicate CorrectlyRead<T> (
    buffer: ReadableBuffer,
    res: ReadCorrect<T>,
    inversionFunction: T -> seq<uint8>
  )
  {
    res.Success?
    ==>
      && var SuccessfulRead(thing, tail) := res.value;
      && CorrectlyReadRange(buffer, tail)
      && inversionFunction(thing) <= buffer.bytes[buffer.start..]
      && tail.start == buffer.start + |inversionFunction(thing)|
  }

  // Sequence ranges are complicated in Dafny.
  // By separating out the sub sequence
  // (the bytes under consideration)
  // it is easer to prove associativity.
  // See: ConsecutiveReadsAreAssociative
  // e.g. bytes[start..stop] == bytes[start..mid] + bytes[mid..stop];
  predicate CorrectlyReadRange(
    buffer: ReadableBuffer,
    tail: ReadableBuffer
  )
  {
    && buffer.bytes == tail.bytes
    && buffer.start <= tail.start <= |tail.bytes|
    && buffer.bytes[buffer.start..] == tail.bytes[buffer.start..]
  }

  // This function is trivial,
  // but it lets `Read` have a `Write` function
  // for its `CorrectlyRead` ensures clause.
  // This facilitates proof
  // because both sides use exactly the same function.
  function method Write(
    data: seq<uint8>
  )
    :(res: seq<uint8>)
    ensures data == res
  {
    data
  }

  function method {:opaque} Read(
    buffer: ReadableBuffer,
    length: nat
  ):
    (res: ReadBinaryCorrect<seq<uint8>>)
    // Optional elements in a data structure can be represented with a length of 0 bytes.
    ensures
      && |buffer.bytes| >= buffer.start + length
    ==>
      && res.Success?
    ensures
      && |buffer.bytes| < buffer.start + length
    ==>
      && res.Failure?
      && res.error.MoreNeeded?
      && res.error.pos == buffer.start + length
    ensures CorrectlyRead(buffer, res, Write)
    ensures res.Success?
    ==>
      var SuccessfulRead(thing, tail) := res.value;
      && |thing| == length
      && tail.start == buffer.start + length
      && tail.bytes[buffer.start..tail.start] == thing
  {
    var end := buffer.start + length;
    :- Need(|buffer.bytes| >= end, MoreNeeded(end));

    Success(SuccessfulRead(
      buffer.bytes[buffer.start..end],
      buffer.(start := end)))
  }

  function method WriteUint16(
    number: uint16
  )
    :(ret: seq<uint8>)
  {
    Write(UInt16ToSeq(number))
  }

  // Opaque? Because the body is not interesting...
  function method ReadUInt16(
    buffer: ReadableBuffer
  )
    :(res: ReadBinaryCorrect<uint16>)
    ensures buffer.start + 2 <= |buffer.bytes| ==> res.Success?
    ensures CorrectlyRead(buffer, res, WriteUint16)
  {
    var SuccessfulRead(uint16Bytes, tail) :- Read(buffer, 2);
    Success(SuccessfulRead(SeqToUInt16(uint16Bytes), tail))
  }

  function method WriteUint32(
    number: uint32
  )
    :(ret: seq<uint8>)
  {
    Write(UInt32ToSeq(number))
  }

  function method ReadUInt32(
    buffer: ReadableBuffer
  ):
    (res: ReadBinaryCorrect<uint32>)
    ensures buffer.start + 4 <= |buffer.bytes| ==> res.Success?
    ensures CorrectlyRead(buffer, res, WriteUint32)
  {
    var SuccessfulRead(uint32Bytes, tail) :- Read(buffer, 4);
    Success(SuccessfulRead(SeqToUInt32(uint32Bytes), tail))
  }

  function method WriteUint64(
    number: uint64
  )
    :(ret: seq<uint8>)
  {
    Write(UInt64ToSeq(number))
  }

  function method ReadUInt64(
    buffer: ReadableBuffer
  ):
    (res: ReadBinaryCorrect<uint64>)
    ensures buffer.start + 8 <= |buffer.bytes| ==> res.Success?
    ensures CorrectlyRead(buffer, res, UInt64ToSeq)
  {
    var SuccessfulRead(uint64Bytes, tail) :- Read(buffer, 8);
    Success(SuccessfulRead(SeqToUInt64(uint64Bytes), tail))
  }

  function method WriteShortLengthSeq(
    d: Uint8Seq16
  )
    :(res: seq<uint8>)
  {
    WriteUint16((|d| as uint16))
    + Write(d)
  }

  function method ReadShortLengthSeq(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<Uint8Seq16>)
    ensures CorrectlyRead(buffer, res, WriteShortLengthSeq)
  {
    var length :- ReadUInt16(buffer);
    var d: SuccessfulRead<Uint8Seq16> :- Read(length.tail, length.data as nat);
    Success(d)
  }

  function method WriteUint32Seq(
    d: Uint8Seq32
  )
    :(res: seq<uint8>)
  {
    WriteUint32(|d| as uint32)
    + Write(d)
  }

  function method ReadUint32Seq(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<Uint8Seq32>)
    ensures CorrectlyRead(buffer, res, WriteUint32Seq)
  {
    var length :- ReadUInt32(buffer);
    var d: SuccessfulRead<Uint8Seq32> :- Read(length.tail, length.data as nat);
    Success(d)
  }

  function method WriteUint64Seq(
    d: Uint8Seq64
  )
    :(res: seq<uint8>)
  {
    WriteUint64(|d| as uint64)
    + Write(d)
  }

  function method ReadUint64Seq(
    buffer: ReadableBuffer
  ):
    (res: ReadCorrect<Uint8Seq64>)
    ensures CorrectlyRead(buffer, res, WriteUint64Seq)
  {
    var length :- ReadUInt64(buffer);
    var d: SuccessfulRead<Uint8Seq64> :- Read(length.tail, length.data as nat);
    Success(d)
  }

  // Combining consecutive reads can be problematic for Dafny to prove `CorrectlyRead`.
  // This lemma aims to simplify this
  // by proving that the total bytes read is equal to the sum of all `Read` calls.
  // This lemma works for any function
  // that uses `Read`, `CorrectlyRead` and `CorrectlyReadRange`
  // as the basis for its correctness.
  // A simple example is to prove the following assert:
  // 
  //  var first :- Read(buffer, a);
  //  var second :- Read(buffer, b);
  //  var third :- Read(buffer, c);
  //  var fourth :- Read(buffer, d);
  //  assert fourth.tail.data[buffer.start..fourth.tail]
  //  == fourth.tail.data[buffer.start..first.tail.start]
  //  + fourth.tail.data[first.tail.start..second.tail.start]
  //  + fourth.tail.data[second.tail.start..third.tail.start]
  //  + fourth.tail.data[third.tail.start..fourth.tail.start]
  lemma ConsecutiveReadsAreAssociative(positions: seq<ReadableBuffer>)
    requires |positions| >= 2
    requires forall i,j
    | 0 <= i < j < |positions| && i + 1 == j
    :: CorrectlyReadRange(positions[i], positions[j])

    ensures PositionsAreConsecutive(positions)
    ensures
      var readableRanges := PositionsToReadableRanges(positions);
    && ReadRange((Seq.First(positions), Seq.Last(positions)))
    == ConcatenateRanges(readableRanges)
  {
    ConsecutiveCorrectlyReadPositionsAreAllConsecutivePositions(positions);
    assert PositionsAreConsecutive(positions);

    if |positions| == 2 {
      assert PositionsToReadableRanges(positions) == [(positions[0], positions[1])];
      assert ReadRange((Seq.First(positions), Seq.Last(positions))) == ConcatenateRanges(PositionsToReadableRanges(positions));
    } else {
      var tail := Seq.Last(positions);
      var left := Seq.DropLast(positions);

      assert ReadRange((Seq.First(positions),  Seq.Last(positions)))
      == ReadRange((Seq.First(positions), Seq.Last(left))) + ReadRange((Seq.Last(left), tail));
      Seq.LemmaLast(positions);

      assert PositionsToReadableRanges(positions) == PositionsToReadableRanges(left) + [(Seq.Last(left), tail)];
      assert ConcatenateRanges(PositionsToReadableRanges(positions)) == ConcatenateRanges(PositionsToReadableRanges(left)) + ReadRange((Seq.Last(left), tail));

      ConsecutiveReadsAreAssociative(Seq.DropLast(positions));
    }
  }

  // This ensures that all the `start` positions
  // in the seq of ReadableBuffer
  // are moving "down" the binary data without gaps.
  // The goal is that these positions
  // come from a sequence of consecutive `Read`
  // or more complicated `Read*` calls.
  predicate PositionsAreConsecutive(
    positions: seq<ReadableBuffer>
  )
  {
    forall i,j
    | 0 <= i < j < |positions|
    :: CorrectlyReadRange(positions[i], positions[j])
  }

  // Since each position is consecutive it represents the "end of a read".
  // This means that each consecutive pair of positions is a read,
  // and therefore represents a range.
  // e.g. the start of the last read to the start of the next read.
  // This function translates these positions into these ranges.
  function PositionsToReadableRanges(positions: seq<ReadableBuffer>)
    :(ranges: seq<(ReadableBuffer, ReadableBuffer)>)
    requires |positions| >= 2
    requires PositionsAreConsecutive(positions)

    ensures |ranges| == |positions| - 1
    ensures Seq.First(positions) == Seq.First(ranges).0
    ensures Seq.Last(positions) == Seq.Last(ranges).1
    // There MUST NOT be any gap between ranges.
    // The end of one range MUST be the start of the next.
    ensures forall i,j
    | 0 <= i < j < |ranges| && i + 1 == j
    :: ranges[i].1 == ranges[j].0
    ensures forall i
    | 0 <= i < |ranges|
    :: CorrectlyReadRange(ranges[i].0, ranges[i].1)
  {
    Seq.Zip(
      Seq.DropLast(positions),
      Seq.DropFirst(positions))
  }

  // Given a sequence of ranges this function will concatenate them.
  // This function simplifies this concatenation
  // in a way that makes it easy to prove
  // that it is equal to the "complete range"
  // e.g. the very first read position, to the very last read position.
  function ConcatenateRanges(ranges: seq<(ReadableBuffer, ReadableBuffer)>)
    :(ret: seq<uint8>)
    requires forall i,j
    | 0 <= i < j < |ranges| && i + 1 == j
    :: ranges[i].1 == ranges[j].0
    requires forall i
    | 0 <= i < |ranges|
    :: CorrectlyReadRange(ranges[i].0, ranges[i].1)
    ensures if |ranges| == 0 then
      ret == []
    else
      ret == ConcatenateRanges(Seq.DropLast(ranges)) + ReadRange(Seq.Last(ranges))
  {
    if |ranges| == 0 then
      []
    else
      ConcatenateRanges(Seq.DropLast(ranges)) + ReadRange(Seq.Last(ranges))
  }

  // Given a range, please read it.
  // Just sugar to make things more readable.
  function ReadRange(
    range: (ReadableBuffer, ReadableBuffer)
  )
    :(ret: seq<uint8>)
    requires CorrectlyReadRange(range.0, range.1)
  {
    range.1.bytes[range.0.start..range.1.start]
  }

  function MoveStart(
    buffer: ReadableBuffer,
    length: nat
  )
    :(ret: ReadableBuffer)
  {
    buffer.(start := buffer.start + length)
  }

  lemma ConsecutiveCorrectlyReadPositionsAreAllConsecutivePositions(positions: seq<ReadableBuffer>)
    requires forall i,j
    | 0 <= i < j < |positions| && i + 1 == j
    :: CorrectlyReadRange(positions[i], positions[j])
    ensures PositionsAreConsecutive(positions)
  {
    forall i,j
    | 0 <= i < j < |positions|
    ensures CorrectlyReadRange(positions[i], positions[j])
    {
      SequentialCorrectlyReadRangesAreTransitive(positions, i, j);
    }
  }

  lemma SequentialCorrectlyReadRangesAreTransitive(
    positions: seq<ReadableBuffer>,
    i: nat,
    j: nat
  )
    requires forall i,j
    | 0 <= i < j < |positions| && i + 1 == j
    :: CorrectlyReadRange(positions[i], positions[j])
    requires i < j < |positions|
    ensures CorrectlyReadRange(positions[i], positions[j])
  {
    if i + 1 == j{
    } else {
      SequentialCorrectlyReadRangesAreTransitive(positions, i, j - 1);
      assert CorrectlyReadRange(positions[i], positions[j-1]);
      assert CorrectlyReadRange(positions[j-1], positions[j]);
      ConsecutiveCorrectlyReadPositionsAreTransitive(positions[i], positions[j-1], positions[j]);
    }
  }

  lemma ConsecutiveCorrectlyReadPositionsAreTransitive(
    start: ReadableBuffer,
    mid: ReadableBuffer,
    end: ReadableBuffer
  )
    requires CorrectlyReadRange(start, mid)
    requires CorrectlyReadRange(mid, end)
    ensures CorrectlyReadRange(start, end)
  {
  }

  // Completeness Lemmas to prove that ReadX/WriteX are both sound and complete

  lemma ReadIsComplete(
    data: seq<uint8>,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<seq<uint8>>)
    requires
      && Write(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == Read(buffer, |bytes|)
  {
    return Read(buffer, |Write(data)|).value;
  }

  lemma ReadUInt16IsComplete(
    data: uint16,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<uint16>)
    requires
      && WriteUint16(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadUInt16(buffer)
  {
    return ReadUInt16(buffer).value;
  }

  lemma ReadUInt32IsComplete(
    data: uint32,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<uint32>)
    requires
      && WriteUint32(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadUInt32(buffer)
  {
    return ReadUInt32(buffer).value;
  }

  lemma ReadUInt64IsComplete(
    data: uint64,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<uint64>)
    requires
      && WriteUint64(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadUInt64(buffer)
  {
    return ReadUInt64(buffer).value;
  }

  lemma ReadShortLengthSeqIsComplete(
    data: Uint8Seq16,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<Uint8Seq16>)
    requires
      && WriteShortLengthSeq(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadShortLengthSeq(buffer)
  {
    assert bytes == WriteUint16(|data| as uint16) + Write(data);
    assert bytes[..|WriteUint16(|data| as uint16)|] == WriteUint16(|data| as uint16);
    var continuation := ReadUInt16IsComplete(|data| as uint16, WriteUint16(|data| as uint16), buffer);
    var tail := ReadIsComplete(data, Write(data), continuation.tail);
    assert tail.data == data;

    return ReadShortLengthSeq(buffer).value;
  }

  lemma ReadUint32SeqIsComplete(
    data: Uint8Seq32,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<Uint8Seq32>)
    requires
      && WriteUint32Seq(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadUint32Seq(buffer)
  {
    assert bytes == WriteUint32(|data| as uint32) + Write(data);
    assert bytes[..|WriteUint32(|data| as uint32)|] == WriteUint32(|data| as uint32);
    var continuation := ReadUInt32IsComplete(|data| as uint32, WriteUint32(|data| as uint32), buffer);
    var tail := ReadIsComplete(data, Write(data), continuation.tail);
    assert tail.data == data;

    return ReadUint32Seq(buffer).value;
  }

  lemma ReadUint64SeqIsComplete(
    data: Uint8Seq64,
    bytes: seq<uint8>,
    buffer: ReadableBuffer
  )
    returns (ret: SuccessfulRead<Uint8Seq64>)
    requires
      && WriteUint64Seq(data) == bytes
      && buffer.start <= |buffer.bytes|
      && bytes <= buffer.bytes[buffer.start..]
    ensures 
      && ReadUint64Seq(buffer).Success?
      && ReadUint64Seq(buffer).value.data == data
      && ReadUint64Seq(buffer).value.tail.start == buffer.start + |bytes|
    ensures
      && ret.data == data
      && ret.tail.start == buffer.start + |bytes|
      && Success(ret) == ReadUint64Seq(buffer)
  {
    assert bytes == WriteUint64(|data| as uint64) + Write(data);
    assert bytes[..|WriteUint64(|data| as uint64)|] == WriteUint64(|data| as uint64);
    var continuation := ReadUInt64IsComplete(|data| as uint64, WriteUint64(|data| as uint64), buffer);
    var tail := ReadIsComplete(data, Write(data), continuation.tail);
    assert tail.data == data;

    return ReadUint64Seq(buffer).value;
  }

}
