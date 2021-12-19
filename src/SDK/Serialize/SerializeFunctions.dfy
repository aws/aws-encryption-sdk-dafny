// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module SerializeFunctions {
  import opened Aws.Crypto
  import opened Seq
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

  
  datatype ReadableBytes = ReadableBytes(
    data: seq<uint8>,
    start: nat
  )
  datatype Data<T> = Data(
    thing: T,
    tail: ReadableBytes
  )

  // Think about a type
  // datatype Thing = Thing(data: s:seq<uint8>, pos: nat)
  // Then we take and return this thing,
  // not just `pos`.
  // Currently we use a tuple,
  // but a more complete datatype like above may be better long term.
  type ReadResult<T, E> = Result<Data<T>, E>
  type ReadCorrect<T> = ReadResult<T, ReadProblems>
  // When reading binary it can not be incorrect.
  // It may not be enough data, but since it is raw binary,
  // it can not be wrong.
  // Generally this T is `seq<uint8>`,
  // but in the a few cases like uint16, uint32, uint64
  // it may be other types.
  type ReadBinaryCorrect<T> = ReadResult<T, MoreNeeded>

  predicate CorrectlyRead<T> (
    bytes: ReadableBytes,
    res: ReadCorrect<T>,
    invertT: T -> seq<uint8>
  )
  {
    res.Success?
    ==>
      && var Data(thing, tail) := res.value;
      && tail.data == bytes.data
      && |tail.data| >= tail.start >= bytes.start
      && invertT(thing) == tail.data[bytes.start..tail.start]
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
  {
    data
  }

  function method Read(
    bytes: ReadableBytes,
    length: nat
  ):
    (res: ReadBinaryCorrect<seq<uint8>>)
    // It may seem strange to alow reading 0 bytes
    // however given compositional it is much more common than you might think.
    // Optional elements in a data structure can be represented with a length of 0 bytes.
    ensures
      && |bytes.data| >= bytes.start + length
    ==>
      && res.Success?
      && var Data(thing, tail) := res.value;
      && tail.data == bytes.data
      && |thing| == length
      && tail.start == bytes.start + length >= 0
      && |tail.data| >= tail.start >= bytes.start
      && tail.data[bytes.start..tail.start] == thing
    ensures
      && |bytes.data| < bytes.start + length
    ==>
      && res.Failure?
      && res.error.MoreNeeded?
      && res.error.pos == bytes.start + length
    ensures CorrectlyRead(bytes, res, Write)
  {
    var end := bytes.start + length;
    if |bytes.data| >= end then
      Success(Data(
        bytes.data[bytes.start..end],
        bytes.(start := end)))
    else
      Failure(MoreNeeded(end))
  }

  // Opaque? Because the body is not interesting...
  function method ReadUInt16(
    bytes: ReadableBytes
  )
    :(res: ReadBinaryCorrect<uint16>)
    ensures CorrectlyRead(bytes, res, UInt16ToSeq)
  {
    var Data(uint16Bytes, tail) :- Read(bytes, 2);
    Success(Data(SeqToUInt16(uint16Bytes), tail))
  }

  function method ReadUInt32(
    bytes: ReadableBytes
  ):
    (res: ReadBinaryCorrect<uint32>)
    ensures CorrectlyRead(bytes, res, UInt32ToSeq)
  {
    var Data(uint32Bytes, tail) :- Read(bytes, 4);
    Success(Data(SeqToUInt32(uint32Bytes), tail))
  }

  function method ReadUInt64(
    bytes: ReadableBytes
  ):
    (res: ReadBinaryCorrect<uint64>)
    ensures CorrectlyRead(bytes, res, UInt64ToSeq)
  {
    var Data(uint64Bytes, tail) :- Read(bytes, 8);
    Success(Data(SeqToUInt64(uint64Bytes), tail))
  }

  function method WriteShortLengthSeq(
    d: Uint8Seq16
  )
    :(res: seq<uint8>)
  {
    UInt16ToSeq(|d| as uint16) + d
  }

  function method ReadShortLengthSeq(
    bytes: ReadableBytes
  ):
    (res: ReadCorrect<Uint8Seq16>)
    ensures CorrectlyRead(bytes, res, WriteShortLengthSeq)
  {
    var Data(length, dataPos) :- ReadUInt16(bytes);
    :- Need(length > 0, Error("Length cannot be 0."));
    Read(dataPos, length as nat)
  }
}
