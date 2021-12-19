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
  import opened EncryptionContext2
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF
                                        //  0x1_0000_0000
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := 1

  type RegularFrameSequenceNumber = n: uint32
  | n  < ENDFRAME_SEQUENCE_NUMBER
  witness *

  type FramedHeader = h : Header.Header
  | h.body.contentType.Framed?
  witness *

  datatype Frame' = 
  | RegularFrame(
    header: FramedHeader,
    seqNum: RegularFrameSequenceNumber,
    iv: seq<uint8>,
    encContent: Uint8Seq32,
    authTag: seq<uint8>)
  | FinalFrame (
    header: FramedHeader,
    finalSequenceNumber: uint32,
    iv: seq<uint8>,
    encContent: Uint8Seq32,
    authTag: seq<uint8>)

  type Frame = f: Frame'
  |
    && |f.iv| == f.header.suite.encrypt.ivLength as nat
    && |f.authTag| == f.header.suite.encrypt.tagLength as nat
  witness *

  datatype NonFramed = NonFramed(
    iv: seq<uint8>,
    encContent: seq<uint8>,
    authTag: seq<uint8>
  )

  function method WriteFrame(
    frame: Frame
  )
    :(ret: seq<uint8>)
    ensures 4  <= |ret|
    ensures ret[0..4] != UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
    ==>
      frame.RegularFrame?
    ensures ret[0..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
    ==>
      frame.FinalFrame?
    ensures
      frame.RegularFrame?
    ==>
      && ret == UInt32ToSeq(frame.seqNum)
        + Write(frame.iv)
        + Write(frame.encContent)
        + Write(frame.authTag)
    ensures
      frame.FinalFrame?
    ==>
      && ret == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
        + UInt32ToSeq(frame.finalSequenceNumber)
        + Write(frame.iv)
        + UInt32ToSeq(|frame.encContent| as uint32)
        + Write(frame.encContent)
        + Write(frame.authTag)


    // ensures 4  <= |ret|
    // ensures
    //   ret[0..4] != UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
    // ==>
    //   && frame.RegularFrame?
    //   && ret == UInt32ToSeq(frame.seqNum)
    //     + Write(frame.iv)
    //     + Write(frame.encContent)
    //     + Write(frame.authTag)
    // ensures
    //   ret[0..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
    // ==>
    //   && frame.FinalFrame?
    //   && ret == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
    //     + UInt32ToSeq(frame.finalSequenceNumber)
    //     + Write(frame.iv)
    //     + UInt32ToSeq(|frame.encContent| as uint32)
    //     + Write(frame.encContent)
    //     + Write(frame.authTag)

  {
    match frame
      case RegularFrame(_, seqNum, iv, encContent, authTag) =>
        UInt32ToSeq(seqNum)
        + Write(iv)
        + Write(encContent)
        + Write(authTag)
      case FinalFrame(_, finalSequenceNumber, iv, encContent, authTag) =>
        UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
        + UInt32ToSeq(finalSequenceNumber)
        + Write(iv)
        + UInt32ToSeq(|encContent| as uint32)
        + Write(encContent)
        + Write(authTag)
  }

  function method ReadFrame(
    bytes: ReadableBytes,
    header: FramedHeader
  )
    :(res: ReadCorrect<Frame>)
    ensures CorrectlyRead(bytes, res, WriteFrame)
  {
    var sequenceNumber :- ReadUInt32(bytes);

    if sequenceNumber.thing != ENDFRAME_SEQUENCE_NUMBER then
      var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
      var encContent :- Read(iv.tail, header.body.frameLength as nat);
      var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

      var regularFrame: Frame := Frame'.RegularFrame(
        header,
        sequenceNumber.thing,
        iv.thing,
        encContent.thing,
        authTag.thing
      );

      assert WriteFrame(regularFrame)[0..4] != UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
      assert CorrectlyRead(bytes, Success(Data(regularFrame, authTag.tail)), WriteFrame);
      Success(Data(regularFrame, authTag.tail))
    else
      var finalSequenceNumber :- ReadUInt32(sequenceNumber.tail);
      var iv :- Read(finalSequenceNumber.tail, header.suite.encrypt.ivLength as nat);
      var contentLength :- ReadUInt32(iv.tail);
      var encContent :- Read(contentLength.tail, contentLength.thing as nat);
      var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

      var finalFrame: Frame := Frame'.FinalFrame(
        header,
        finalSequenceNumber.thing,
        iv.thing,
        encContent.thing,
        authTag.thing
      );

      assert WriteFrame(finalFrame)[0..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
      assert CorrectlyRead(bytes, Success(Data(finalFrame, authTag.tail)), WriteFrame);
      Success(Data(finalFrame, authTag.tail))
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
    // Uint64 Length
    + Write(nonFramed.encContent)
    + Write(nonFramed.authTag)
  }



}
