// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "Header.dfy"
include "EncryptionContext.dfy"
include "EncryptedDataKeys.dfy"

module Frames {
  import Aws.Crypto
  import Seq
  import Header
  import MaterialProviders.Client
  import opened EncryptedDataKeys
  import opened EncryptionContext
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := 1

  type FramedHeader = h : Header.Header
  | h.body.contentType.Framed?
  witness *

  type NonFramedHeader = h : Header.Header
  | h.body.contentType.NonFramed?
  witness *

  datatype Frame = 
  | RegularFrame(
    header: Header.Header,
    seqNum: uint32,
    iv: seq<uint8>,
    encContent: seq<uint8>,
    authTag: seq<uint8>)
  | FinalFrame (
    header: Header.Header,
    seqNum: uint32,
    iv: seq<uint8>,
    encContent: seq<uint8>,
    authTag: seq<uint8>)
  | NonFramed(
    header: Header.Header,
    iv: seq<uint8>,
    encContent: seq<uint8>,
    authTag: seq<uint8>
  )

  predicate IvTagLengths(frame: Frame){
    && |frame.iv| == frame.header.suite.encrypt.ivLength as nat
    && |frame.authTag| == frame.header.suite.encrypt.tagLength as nat
  }

  predicate IsRegularFrame(frame: Frame){
    && frame.RegularFrame?
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    && |frame.encContent| == frame.header.body.frameLength as nat
    && frame.seqNum != ENDFRAME_SEQUENCE_NUMBER
  }

  type RegularFrame = frame: Frame
  | IsRegularFrame(frame)
  witness *

  predicate IsFinalFrame(frame: Frame) {
    && frame.FinalFrame?
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    && |frame.encContent| <= frame.header.body.frameLength as nat
  }

  type FinalFrame = frame: Frame
  | IsFinalFrame(frame)
  witness *

  type NonFramed = frame: Frame
  |
    && frame.NonFramed?
    && IvTagLengths(frame)
    && frame.header.body.contentType.NonFramed?
    && |frame.encContent| < SAFE_MAX_ENCRYPT
  witness *
  
  const SAFE_MAX_ENCRYPT := 0xFFFFFFFE0 // 2^36 - 32

  function method WriteRegularFrame(
    regularFrame: RegularFrame
  )
    :(ret: seq<uint8>)
    ensures
      && ReadUInt32(ReadableBytes(ret, 0)).Success?
      && ReadUInt32(ReadableBytes(ret, 0)).value.thing != ENDFRAME_SEQUENCE_NUMBER
  {
    WriteUint32(regularFrame.seqNum)
    + Write(regularFrame.iv)
    + Write(regularFrame.encContent)
    + Write(regularFrame.authTag)
  }

  function method ReadRegularFrame(
    bytes: ReadableBytes,
    header: FramedHeader
  )
    :(res: ReadCorrect<RegularFrame>)
    ensures res.Success?
    ==>
      && var Data(thing, tail) := res.value;
      && tail.data == bytes.data
      && |tail.data| >= tail.start >= bytes.start
      && bytes.data[bytes.start..tail.start] == tail.data[bytes.start..tail.start]
      && WriteRegularFrame(thing) == tail.data[bytes.start..tail.start]
    ensures CorrectlyRead(bytes, res, WriteRegularFrame)
  {

    var sequenceNumber :- ReadUInt32(bytes);
    :- Need(sequenceNumber.thing != ENDFRAME_SEQUENCE_NUMBER, Error("bad"));

    var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
    var encContent :- Read(iv.tail, header.body.frameLength as nat);
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

    var regularFrame: RegularFrame := Frame.RegularFrame(
      header,
      sequenceNumber.thing,
      iv.thing,
      encContent.thing,
      authTag.thing
    );

    Success(Data(regularFrame, authTag.tail))
  }

  function method WriteFinalFrame(
    finalFrame: FinalFrame
  )
    :(ret: seq<uint8>)
    ensures 
      && ReadUInt32(ReadableBytes(ret, 0)).Success?
      && ReadUInt32(ReadableBytes(ret, 0)).value.thing == ENDFRAME_SEQUENCE_NUMBER
  {
    WriteUint32(ENDFRAME_SEQUENCE_NUMBER)
    + WriteUint32(finalFrame.seqNum)
    + Write(finalFrame.iv)
    + WriteUint32Seq(finalFrame.encContent)
    + Write(finalFrame.authTag)
  }

  function method ReadFinalFrame(
    bytes: ReadableBytes,
    header: FramedHeader
  )
    :(res: ReadCorrect<FinalFrame>)
    ensures res.Success?
    ==>
      && var Data(thing, tail) := res.value;
      && tail.data == bytes.data
      && |tail.data| >= tail.start >= bytes.start
      && bytes.data[bytes.start..tail.start] == tail.data[bytes.start..tail.start]
      && WriteFinalFrame(thing) == tail.data[bytes.start..tail.start]
    ensures CorrectlyRead(bytes, res, WriteFinalFrame)
  {
    var finalFrameSignal :- ReadUInt32(bytes);
    :- Need(finalFrameSignal.thing == ENDFRAME_SEQUENCE_NUMBER, Error("bad"));

    var sequenceNumber :- ReadUInt32(finalFrameSignal.tail);
    var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
    var encContent :- ReadUint32Seq(iv.tail);
    :- Need(|encContent.thing| as uint32 <= header.body.frameLength, Error("bad"));
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

    var finalFrame: FinalFrame := Frame.FinalFrame(
      header,
      sequenceNumber.thing,
      iv.thing,
      encContent.thing,
      authTag.thing
    );

    Success(Data(finalFrame, authTag.tail))
  }

  function method ReadNonFrame(
    bytes: ReadableBytes,
    header: NonFramedHeader
  )
    :(res: ReadCorrect<NonFramed>)
    ensures res.Success?
    ==>
      && var Data(thing, tail) := res.value;
      && tail.data == bytes.data
      && |tail.data| >= tail.start >= bytes.start
      && bytes.data[bytes.start..tail.start] == tail.data[bytes.start..tail.start]
      && WriteNonFramed(thing) == tail.data[bytes.start..tail.start]
    ensures CorrectlyRead(bytes, res, WriteNonFramed)
  {
    var iv :- Read(bytes, header.suite.encrypt.ivLength as nat);
    // Checking only the content length _before_ reading it into memory
    // is just a nice thing to do given the sizes involved.
    var contentLength :- ReadUInt64(iv.tail);
    :- Need(contentLength.thing as nat < SAFE_MAX_ENCRYPT, Error("Too Much"));
    var encContent :- ReadUint64Seq(iv.tail);
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

    var nonFramed: NonFramed := Frame.NonFramed(
      header,
      iv.thing,
      encContent.thing,
      authTag.thing
    );

    Success(Data(nonFramed, authTag.tail))
  }

  // The Encryption SDK no longer supports writing Non-Framed Data.
  // That is why this is a function and not a function method.
  // This is here to support correct reading of Non-Framed Data.
  function WriteNonFramed(
    nonFramed: NonFramed
  )
    :(ret: seq<uint8>)
  {
    Write(nonFramed.iv)
    + WriteUint64Seq(nonFramed.encContent)
    + Write(nonFramed.authTag)
  }

}
