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
    | MoreNeeded(pos: nat)
    | Error(message: string)
  type MoreNeeded = p: ReadProblems | p.MoreNeeded? witness *

  // Think about a type
  // datatype Thing = Thing(data: s:seq<uint8>, pos: nat)
  // Then we take and return this thing,
  // not just `pos`.
  type ReadResult<T, E> = Result<(T, nat), E>
  type ReadCorrect<T> = ReadResult<T, ReadProblems>
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
    l: nat
  ):
    (res: ReadBinary<seq<uint8>>)
    decreases if pos > 0 then true else false
    requires l > 0
    ensures
      && |s| >= pos + l
    ==>
      && res.Success?
      && |res.value.0| == l
      && res.value.1 == pos + l >= 0
      && |s| >= res.value.1 > pos
      && s[pos..res.value.1] == res.value.0
    ensures
      && pos + l > |s|
    ==>
      && res.Failure?
      && res.error.MoreNeeded?
      && res.error.pos == pos + l
    ensures CorrectlyRead(s, pos, res, d => d)
  {
    var end := pos + l;
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
    // decreases if pos > 0 then true else false
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
