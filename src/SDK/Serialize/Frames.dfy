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

  //= compliance/client-apis/encrypt.txt#2.7.1
  //= type=implication
  //# If this is the first frame sequentially, this
  //# value MUST be 1.
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
    //= compliance/data-format/message-body.txt#2.5.1.1
    //= type=implication
    //# The
    //# IV MUST be a unique IV within the message.
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
    //= compliance/data-format/message-body.txt#2.5.2.1.4
    //= type=implication
    //# The authentication tag length MUST be equal to the authentication tag
    //# length of the algorithm suite specified by the Algorithm Suite ID
    //# (message-header.md#algorithm-suite-id) field.
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    //= compliance/data-format/message-body.txt#2.5.2.1.3
    //= type=implication
    //# The length of the encrypted content of a Regular Frame MUST be equal
    //# to the Frame Length.
    && |frame.encContent| == frame.header.body.frameLength as nat
    && frame.seqNum != ENDFRAME_SEQUENCE_NUMBER
  }

  type RegularFrame = frame: Frame
  | IsRegularFrame(frame)
  witness *

  predicate IsFinalFrame(frame: Frame) {
    && frame.FinalFrame?
    //= compliance/data-format/message-body.txt#2.5.2.2.6
    //= type=implication
    //# The authentication tag length MUST be equal to the authentication tag
    //# length of the algorithm suite specified by the Algorithm Suite ID
    //# (message-header.md#algorithm-suite-id) field.
    && IvTagLengths(frame)
    && frame.header.body.contentType.Framed?
    && |frame.encContent| <= frame.header.body.frameLength as nat
  }

  type FinalFrame = frame: Frame
  | IsFinalFrame(frame)
  witness *

  predicate IsNonFramed(frame: Frame) {
    && frame.NonFramed?
    && IvTagLengths(frame)
    && frame.header.body.contentType.NonFramed?
    //= compliance/data-format/message-body.txt#2.5.1.2
    //= type=implication
    //# The length MUST NOT be greater than "2^36 - 32", or 64 gibibytes (64
    //# GiB), due to restrictions imposed by the implemented algorithms
    //# (../framework/algorithm-suites.md).
    && |frame.encContent| < SAFE_MAX_ENCRYPT
  }

  type NonFramed = frame: Frame
  | IsNonFramed(frame)
  witness *

  //= compliance/data-format/message-body.txt#2.5.2
  //= type=implication
  //# *  The total bytes allowed in a single frame MUST be less than or
  //# equal to "2^32 - 1".
  lemma LemmaRegularOrFinalFrameHasUint32ContentByteLength(frame: Frame)
    ensures IsRegularFrame(frame) || IsFinalFrame(frame)
      ==> |frame.encContent| <= 0xFFFF_FFFF
  {}

  const SAFE_MAX_ENCRYPT := 0xFFFFFFFE0 // 2^36 - 32

  function method WriteRegularFrame(
    regularFrame: RegularFrame
  )
    :(ret: seq<uint8>)
    ensures
      && ReadUInt32(ReadableBuffer(ret, 0)).Success?
      && ReadUInt32(ReadableBuffer(ret, 0)).value.data != ENDFRAME_SEQUENCE_NUMBER
  {
    WriteUint32(regularFrame.seqNum)
    + (Write(regularFrame.iv)
    + (Write(regularFrame.encContent)
    + (Write(regularFrame.authTag))))
  }

  function method ReadRegularFrame(
    buffer: ReadableBuffer,
    header: FramedHeader
  )
    :(res: ReadCorrect<RegularFrame>)
    ensures res.Success?
    ==> res.value.data.header == header
    ensures CorrectlyRead(buffer, res, WriteRegularFrame)
  {

    var sequenceNumber :- ReadUInt32(buffer);
    :- Need(sequenceNumber.data != ENDFRAME_SEQUENCE_NUMBER, Error("bad"));

    var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
    var encContent :- Read(iv.tail, header.body.frameLength as nat);
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

    var regularFrame: RegularFrame := Frame.RegularFrame(
      header,
      sequenceNumber.data,
      iv.data,
      encContent.data,
      authTag.data
    );

    assert {:split_here} true;
    assert WriteRegularFrame(regularFrame) <= buffer.bytes[buffer.start..];

    Success(SuccessfulRead(regularFrame, authTag.tail))
  }

  function method WriteFinalFrame(
    finalFrame: FinalFrame
  )
    :(ret: seq<uint8>)
    ensures
      && ReadUInt32(ReadableBuffer(ret, 0)).Success?
      //= compliance/data-format/message-body.txt#2.5.2.2.1
      //= type=implication
      //# The value MUST be encoded as the 4 bytes "FF FF FF FF" in hexadecimal
      //# notation.
      && ReadUInt32(ReadableBuffer(ret, 0)).value.data == ENDFRAME_SEQUENCE_NUMBER
  {
    WriteUint32(ENDFRAME_SEQUENCE_NUMBER)
    + (WriteUint32(finalFrame.seqNum)
    + (Write(finalFrame.iv)
    + (WriteUint32Seq(finalFrame.encContent)
    + (Write(finalFrame.authTag)))))
  }

  function method {:vcs_split_on_every_assert} ReadFinalFrame(
    buffer: ReadableBuffer,
    header: FramedHeader
  )
    :(res: ReadCorrect<FinalFrame>)
    ensures res.Success?
    ==> res.value.data.header == header
    ensures CorrectlyRead(buffer, res, WriteFinalFrame)

    //= compliance/client-apis/decrypt.txt#2.7.4
    //= type=implication
    //# If deserializing a final frame (../data-format/message-body.md#final-
    //# frame), this operation MUST ensure that the length of the encrypted
    //# content field is less than or equal to the frame length deserialized
    //# in the message header.
    ensures
      res.Success?
    ==>
      && var finalFrameSignalRes := ReadUInt32(buffer);
      && finalFrameSignalRes.Success?
      && var sequenceNumberRes := ReadUInt32(finalFrameSignalRes.value.tail);
      && sequenceNumberRes.Success?
      && var ivRes := Read(sequenceNumberRes.value.tail, header.suite.encrypt.ivLength as nat);
      && ivRes.Success?
      && var encContentRes := ReadUint32Seq(ivRes.value.tail);
      && encContentRes.Success?
      && |encContentRes.value.data| as uint32 <= header.body.frameLength    

  {
    var finalFrameSignal :- ReadUInt32(buffer);
    :- Need(finalFrameSignal.data == ENDFRAME_SEQUENCE_NUMBER, Error("bad"));

    var sequenceNumber :- ReadUInt32(finalFrameSignal.tail);
    var iv :- Read(sequenceNumber.tail, header.suite.encrypt.ivLength as nat);
    var encContent :- ReadUint32Seq(iv.tail);

    //= compliance/client-apis/decrypt.txt#2.7.4
    //# If deserializing a final frame (../data-format/message-body.md#final-
    //# frame), this operation MUST ensure that the length of the encrypted
    //# content field is less than or equal to the frame length deserialized
    //# in the message header.
    :- Need(|encContent.data| as uint32 <= header.body.frameLength, Error("bad"));
    
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);
    var finalFrame: FinalFrame := Frame.FinalFrame(
      header,
      sequenceNumber.data,
      iv.data,
      encContent.data,
      authTag.data
    );

    assert WriteUint32(finalFrameSignal.data)
    + (WriteUint32(finalFrame.seqNum)
    + (Write(finalFrame.iv)
    + (WriteUint32Seq(finalFrame.encContent)
    + (Write(finalFrame.authTag))))) <= buffer.bytes[buffer.start..];
    assert WriteFinalFrame(finalFrame) <= buffer.bytes[buffer.start..];

    Success(SuccessfulRead(finalFrame, authTag.tail))
  }

  function method ReadNonFrame(
    buffer: ReadableBuffer,
    header: NonFramedHeader
  )
    :(res: ReadCorrect<NonFramed>)
    ensures CorrectlyRead(buffer, res, WriteNonFramed)
  {
    var iv :- Read(buffer, header.suite.encrypt.ivLength as nat);
    // Checking only the content length _before_ reading it into memory
    // is just a nice thing to do given the sizes involved.
    var contentLength :- ReadUInt64(iv.tail);
    :- Need(contentLength.data as nat < SAFE_MAX_ENCRYPT, Error("Too Much"));
    var encContent :- ReadUint64Seq(iv.tail);
    var authTag :- Read(encContent.tail, header.suite.encrypt.tagLength as nat);

    var nonFramed: NonFramed := Frame.NonFramed(
      header,
      iv.data,
      encContent.data,
      authTag.data
    );

    assert {:split_here} true;
    assert WriteNonFramed(nonFramed) <= buffer.bytes[buffer.start..];

    Success(SuccessfulRead(nonFramed, authTag.tail))
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
    + (WriteUint64Seq(nonFramed.encContent)
    + (Write(nonFramed.authTag)))
  }

}
