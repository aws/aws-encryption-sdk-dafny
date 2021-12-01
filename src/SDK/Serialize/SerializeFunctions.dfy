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

  // Think about a type
  // datatype Thing = Thing(data: s:seq<uint8>, pos: nat)
  // Then we take and return this thing,
  // not just `pos`.
  // Currently we use a tuple,
  // but a more complete datatype like above may be better long term.
  type ReadResult<T, E> = Result<(T, nat), E>
  type ReadCorrect<T> = ReadResult<T, ReadProblems>
  // When reading binary it can not be incorrect.
  // It may not be enough data, but since it is raw binary,
  // it can not be wrong.
  // This T MUST be `seq<uint8>`
  type ReadBinary<T> = ReadResult<T, MoreNeeded>

  predicate CorrectlyRead<T> (
    s: seq<uint8>,
    pos: nat,
    res: ReadCorrect<T>,
    invertT: T -> seq<uint8>
  )
  {
    res.Success?
    ==>
      && |s| >= res.value.1 >= pos
      && invertT(res.value.0) == s[pos..res.value.1]
  }

  function method Read(
    s: seq<uint8>,
    pos: nat,
    length: nat
  ):
    (res: ReadBinaryCorrect<seq<uint8>>)
    decreases if pos > 0 then true else false
    requires length > 0
    ensures
      && |s| >= pos + length
    ==>
      && res.Success?
      && |res.value.0| == length
      && res.value.1 == pos + length >= 0
      && |s| >= res.value.1 > pos
      && s[pos..res.value.1] == res.value.0
    ensures
      && pos + length > |s|
    ==>
      && res.Failure?
      && res.error.MoreNeeded?
      && res.error.pos == pos + length
    ensures CorrectlyRead(s, pos, res, d => d)
  {
    var end := pos + length;
    if |s| >= end then
      Success((s[pos..end], end))
    else
      Failure(MoreNeeded(end))
  }

  // Opaque? Because the body is not interesting...
  function method ReadUInt16(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadBinary<uint16>)
    ensures CorrectlyRead(s, pos, res, UInt16ToSeq)
  {
    var (data, end) :- Read(s, pos, 2);
    Success((SeqToUInt16(data), end))
  }

  function method WriteShortLengthSeq(
    d: Uint8Seq16
  ):
    (res: seq<uint8>)
  {
    UInt16ToSeq(|d| as uint16) + d
  }

  function method ReadShortLengthSeq(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<Uint8Seq16>)
    ensures CorrectlyRead(s, pos, res, WriteShortLengthSeq)
  {
    var (length, dataPos) :- ReadUInt16(s, pos);
    :- Need(length > 0, Error("Length cannot be 0."));
    Read(s, dataPos, length as nat)
  }
}
