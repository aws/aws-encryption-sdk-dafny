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

module Frames2 {
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
  // | NonFramed(
  //   header: Header.Header,
  //   iv: seq<uint8>,
  //   encContent: seq<uint8>,
  //   authTag: seq<uint8>
  // )

  predicate IvTagLengths(frame: Frame){
    && |frame.iv| == frame.header.suite.encrypt.ivLength as nat
    && |frame.authTag| == frame.header.suite.encrypt.tagLength as nat
  }

  type RegularFrame = frame: Frame
  |
    && frame.RegularFrame?
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    && |frame.encContent| == frame.header.body.frameLength as nat
    && frame.seqNum != ENDFRAME_SEQUENCE_NUMBER
  witness *

  type FinalFrame = frame: Frame
  |
    && frame.FinalFrame?
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    && |frame.encContent| <= frame.header.body.frameLength as nat
  witness *

  // type NonFramed = frame: Frame
  // |
  //   && frame.NonFramed?
  //   && IvTagLengths(frame)
  //   && frame.header.body.contentType.NonFramed?
  //   && |frame.encContent| < SAFE_MAX_ENCRYPT
  // witness *
  
  const SAFE_MAX_ENCRYPT := 0xFFFFFFFE0 // 2^36 - 32

  function method WriteRegularFrame(
    regularFrame: RegularFrame
  )
    :(ret: seq<uint8>)
    ensures
      && ReadUInt32(ReadableBytes(ret, 0)).Success?
      && ReadUInt32(ReadableBytes(ret, 0)).value.thing != ENDFRAME_SEQUENCE_NUMBER
  {
    UInt32ToSeq(regularFrame.seqNum)
    + regularFrame.iv
    + regularFrame.encContent
    + regularFrame.authTag
  }

  function method ReadRegularFrame(
    bytes: ReadableBytes,
    header: FramedHeader
  )
    :(res: ReadCorrect<RegularFrame>)
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

  // function method WriteFinalFrame(
  //   finalFrame: FinalFrame
  // )
  //   :(ret: seq<uint8>)
  //   ensures 
  //     && ReadUInt32(ReadableBytes(ret, 0)).Success?
  //     && ReadUInt32(ReadableBytes(ret, 0)).value.thing == ENDFRAME_SEQUENCE_NUMBER
  // {
  //   UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
  //   + UInt32ToSeq(finalFrame.seqNum)
  //   + Write(finalFrame.iv)
  //   + UInt32ToSeq(|finalFrame.encContent| as uint32)
  //   + Write(finalFrame.encContent)
  //   + Write(finalFrame.authTag)
  // }

  // function method ReadFinalFrame(
  //   bytes: ReadableBytes,
  //   header: FramedHeader
  // )
  //   :(res: ReadCorrect<FinalFrame>)
  //   ensures
  //     res.Success?
  //   ==>
  //     && var Data(thing, tail) := res.value;
  //     && tail.data == bytes.data
  //     && tail.Tail?
  //     && tail.start == bytes.pos
  //     && |tail.data| >= tail.pos >= bytes.pos
  //     && WriteFinalFrame(thing) == tail.data[tail.start..tail.pos]
  //   // ensures CorrectlyRead(bytes, res, WriteFinalFrame)
  // {
  //   var finalFrameSignal :- ReadUInt32(bytes);
  //   :- Need(finalFrameSignal.thing == ENDFRAME_SEQUENCE_NUMBER, Error("bad"));

  //   var sequenceNumber :- ReadUInt32(finalFrameSignal.tail);
  //   var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
  //   var contentLength :- ReadUInt32(iv.tail);
  //   :- Need(contentLength.thing <= header.body.frameLength, Error("bad"));
  //   var encContent :- Read(contentLength.tail, contentLength.thing as nat);
  //   var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

  //   var finalFrame: FinalFrame := Frame.FinalFrame(
  //     header,
  //     sequenceNumber.thing,
  //     iv.thing,
  //     encContent.thing,
  //     authTag.thing
  //   );

  //   Success(Data(finalFrame, authTag.tail.(start := bytes.pos)))
  // }

  // function method ReadNonFrame(
  //   bytes: ReadableBytes,
  //   header: NonFramedHeader
  // )
  //   :(res: ReadCorrect<NonFramed>)
  //   ensures
  //     res.Success?
  //   ==>
  //     && var Data(thing, tail) := res.value;
  //     && tail.data == bytes.data
  //     && tail.Tail?
  //     && tail.start == bytes.pos
  //     && |tail.data| >= tail.pos >= bytes.pos
  //     && WriteNonFramed(thing) == tail.data[tail.start..tail.pos]
  //   // ensures CorrectlyRead(bytes, res, WriteNonFramed)
  // {
  //   var iv :- Read(bytes, header.suite.encrypt.ivLength as nat);
  //   var contentLength :- ReadUInt64(iv.tail);
  //   :- Need(contentLength.thing as nat < SAFE_MAX_ENCRYPT, Error("Too Much"));
  //   var encContent :- Read(contentLength.tail, contentLength.thing as nat);
  //   var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

  //   var nonFramed: NonFramed := Frame.NonFramed(
  //     header,
  //     iv.thing,
  //     encContent.thing,
  //     authTag.thing
  //   );

  //   Success(Data(nonFramed, authTag.tail.(start := bytes.pos)))
  // }

  // // The Encryption SDK no longer supports writing Non-Framed Data.
  // // That is why this is a function and not a function method.
  // // This is here to support correct reading of Non-Framed Data.
  // function WriteNonFramed(
  //   nonFramed: NonFramed
  // )
  //   :(ret: seq<uint8>)
  // {
  //   Write(nonFramed.iv)
  //   + UInt64ToSeq(|nonFramed.encContent| as uint64)
  //   + Write(nonFramed.encContent)
  //   + Write(nonFramed.authTag)
  // }

}
