// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Serialize/SerializableTypes.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Util/Streams.dfy"
include "../Util/UTF8.dfy"
include "Serialize/Frames.dfy"

include "Serialize/Header.dfy"
include "Serialize/HeaderTypes.dfy"
include "Serialize/V1HeaderBody.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/SerializeFunctions.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"

module MessageBody {
  // export
  //   provides EncryptMessageBody, DecryptFramedMessageBody, DecryptNonFramedMessageBody,
  //     Wrappers, UInt, Streams, Client,
  //     FramesEncryptPlaintext, AESEncryption, DecryptedWithKey
  //   reveals  SeqWithGhostFrames

  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import Streams
  import UTF8
  import SerializableTypes
  import MaterialProviders.Client
  import Frames
  import Header
  import opened SerializeFunctions
  import Seq

  datatype BodyAADContent = AADRegularFrame | AADFinalFrame | AADSingleBlock

  const BODY_AAD_CONTENT_REGULAR_FRAME: string := "AWSKMSEncryptionClient Frame"
  const BODY_AAD_CONTENT_FINAL_FRAME: string := "AWSKMSEncryptionClient Final Frame"
  const BODY_AAD_CONTENT_SINGLE_BLOCK: string := "AWSKMSEncryptionClient Single Block"

  function method BodyAADContentTypeString(bc: BodyAADContent): string {
    match bc
    case AADRegularFrame => BODY_AAD_CONTENT_REGULAR_FRAME
    case AADFinalFrame => BODY_AAD_CONTENT_FINAL_FRAME
    case AADSingleBlock => BODY_AAD_CONTENT_SINGLE_BLOCK
  }

  const START_SEQUENCE_NUMBER: uint32 := Frames.START_SEQUENCE_NUMBER
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := Frames.ENDFRAME_SEQUENCE_NUMBER
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := Frames.NONFRAMED_SEQUENCE_NUMBER

  function method IVSeq(suite: Client.AlgorithmSuites.AlgorithmSuite, sequenceNumber: uint32)
    :(ret: seq<uint8>)
    // The suite dictates the length of the IV
    // this relationship is useful for correctness
    ensures |ret| == suite.encrypt.ivLength as nat
  {
    seq(suite.encrypt.ivLength as int - 4, _ => 0) + UInt32ToSeq(sequenceNumber)
  }

  lemma IVSeqDistinct(suite: Client.AlgorithmSuites.AlgorithmSuite, m: uint32, n: uint32)
    requires m != n
    ensures
      var algorithmSuiteID := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
      && IVSeq(suite, m) != IVSeq(suite, n)
  {
    var paddingLength :=  suite.encrypt.ivLength as int - 4;
    assert IVSeq(suite, m)[paddingLength..] == UInt32ToSeq(m);
    assert IVSeq(suite, n)[paddingLength..] == UInt32ToSeq(n);
    UInt32SeqSerializeDeserialize(m);
    UInt32SeqSerializeDeserialize(n);
  }

  /**
    Predicate states that frames encrypt plaintext

      Plaintext is split into chunks of frameLength. One chunck is encrypted in one frame. Reasoning about chunks makes proving predicate easier
        FramesEncryptPlaintextSegments: States that sequence of frames decrypts to sequence of chunks
        SumPlaintextSegments: States that sum of chunks is the plaintext
   */
  predicate FramesEncryptPlaintext(frames: FramedMessage, plaintext: seq<uint8>)
  {
    exists plaintextSeg: seq<seq<uint8>>
    ::
    && FramesEncryptPlaintextSegments(frames.regularFrames + [frames.finalFrame], plaintextSeg)
    && SumPlaintextSegments(plaintextSeg) == plaintext
  }

  predicate FramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>)
  {
    // The total number of frames MUST equal the total number of plaintext segments.
    if |frames| != |plaintextSeg| then
      false
    else
      // No more regular frames, check the tail
     if frames == [] then
        true
      else
        // Drop the segments
        && FramesEncryptPlaintextSegments(Seq.DropLast(frames), Seq.DropLast(plaintextSeg))
        && AESEncryption.CiphertextGeneratedWithPlaintext(Seq.Last(frames).encContent, Seq.Last(plaintextSeg))
  }

  function SumPlaintextSegments(plaintextSeg: seq<seq<uint8>>): seq<uint8>
  {
    if plaintextSeg == [] then
      []
    else
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg| - 1]) + plaintextSeg[|plaintextSeg| - 1]
  }

  type MessageRegularFrames = regularFrames: seq<Frames.RegularFrame>
  | IsMessageRegularFrames(regularFrames)
  witness *

  predicate MessageFramesAreMonotonic(frames: seq<MessageFrame>){
    if |frames| == 0 then true
    else
      // Cardinality can be thought of as the tail index
      // of a one-based indexed array.
      // Sequence number is the one-based indexed array of frames
      && |frames| == Seq.Last(frames).seqNum as nat
      && MessageFramesAreMonotonic(Seq.DropLast(frames))
  }

  predicate MessageFramesAreForTheSameMessage(frames: seq<MessageFrame>){
    forall i
    // This excludes the First frame in the seq
    // because all headers are definitionally equal for `[]` and `[frame]`.
    | 0 < i < |frames|
    ::  Seq.First(frames).header == frames[i].header
  }

  predicate IsMessageRegularFrames(regularFrames: seq<Frames.RegularFrame>) {
    // The total number of frames MUST be < UINT16_LENGTH.
    // And a RegularFrame can not have a sequence number
    // equal to the ENDFRAME_SEQUENCE_NUMBER.
    && 0 <= |regularFrames| < ENDFRAME_SEQUENCE_NUMBER as nat
    // The sequence number MUST be monotonic
    && MessageFramesAreMonotonic(regularFrames)
    // All frames MUST all be from the same messages i.e. the same header
    && MessageFramesAreForTheSameMessage(regularFrames)
  }

  type NonFramedMessage = Frames.NonFramed

  datatype FramedMessageBody = FramedMessageBody(
    regularFrames: MessageRegularFrames,
    finalFrame: Frames.FinalFrame
  )

  type FramedMessage = body: FramedMessageBody
  |
  && MessageFramesAreMonotonic(body.regularFrames + [body.finalFrame])
  && MessageFramesAreForTheSameMessage(body.regularFrames + [body.finalFrame])
  witness *

  type MessageFrame = frame: Frames.Frame
  |
  || Frames.IsFinalFrame(frame)
  || Frames.IsRegularFrame(frame)
  witness *

  type Frame = frame: Frames.Frame
  |
  || Frames.IsFinalFrame(frame)
  || Frames.IsRegularFrame(frame)
  || Frames.IsFinalFrame(frame)
  witness *

  lemma LemmaAddingNextRegularFrame(
    regularFrames: MessageRegularFrames,
    nextRegularFrame: Frames.RegularFrame
  )
    requires |regularFrames| + 1 < ENDFRAME_SEQUENCE_NUMBER as nat
    requires nextRegularFrame.seqNum as nat == |regularFrames| + 1 as nat
    requires MessageFramesAreForTheSameMessage(regularFrames + [nextRegularFrame])
    ensures IsMessageRegularFrames(regularFrames + [nextRegularFrame])
  {}

  method EncryptMessageBody(
    plaintext: seq<uint8>,
    header : Header.Header,
    key: seq<uint8>
  )
    returns (result: Result<FramedMessage, string>)
    requires |key| ==  header.suite.encrypt.keyLength as nat
    requires 0 < header.body.frameLength as nat < UINT32_LIMIT
    requires header.body.contentType.Framed?
    ensures match result
      case Failure(e) => true
      case Success(body) =>
        && (forall frame: Frames.Frame
          | frame in body.regularFrames
          :: AESEncryption.EncryptedWithKey(frame.encContent, key))
        && AESEncryption.EncryptedWithKey(body.finalFrame.encContent, key)
  {
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    var regularFrames: MessageRegularFrames := [];

    while n + header.body.frameLength as nat < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant |regularFrames| == (sequenceNumber - START_SEQUENCE_NUMBER) as nat
      invariant forall frame: Frames.Frame
      | frame in regularFrames
      ::
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
        && frame.header == header
    {
      :- Need(sequenceNumber < ENDFRAME_SEQUENCE_NUMBER, "too many frames");
      var plaintextFrame := plaintext[n..n + header.body.frameLength as nat];
      var regularFrame :- EncryptRegularFrame(
        key,
        header,
        plaintextFrame,
        sequenceNumber
      );

      assert regularFrame.seqNum as nat == |regularFrames| + 1;
      LemmaAddingNextRegularFrame(regularFrames, regularFrame);

      regularFrames := regularFrames + [regularFrame];
      n, sequenceNumber := n + header.body.frameLength as nat, sequenceNumber + 1;
    }

    var finalFrame :- EncryptFinalFrame(
      key,
      header,
      plaintext[n..],
      sequenceNumber
    );

    assert MessageFramesAreForTheSameMessage(regularFrames + [finalFrame]);

    return Success(FramedMessageBody(
      regularFrames := regularFrames,
      finalFrame := finalFrame
    ));
  }

  method EncryptRegularFrame(
    key: seq<uint8>,
    header: Header.Header,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<Frames.RegularFrame, string>)
    requires |key| == header.suite.encrypt.keyLength as int
    requires 0 < header.body.frameLength as nat < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber < ENDFRAME_SEQUENCE_NUMBER
    requires header.body.contentType.Framed?
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == header.body.frameLength as nat && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    ensures match res
      case Failure(e) => true
      case Success(frame) =>
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
        && frame.seqNum == sequenceNumber
        && frame.header == header
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := IVSeq(header.suite, sequenceNumber);
    var aad := BodyAAD(
      header.body.messageId,
      AADRegularFrame,
      sequenceNumber,
      |plaintext| as uint64
    );

    var encryptionOutput :- AESEncryption.AESEncrypt(
      header.suite.encrypt,
      iv,
      key,
      plaintext,
      aad
    );

    var frame: Frames.RegularFrame := Frames.Frame.RegularFrame(
      header,
      sequenceNumber,
      iv,
      encryptionOutput.cipherText,
      encryptionOutput.authTag
    );

    return Success(frame);
  }

  method EncryptFinalFrame(
    key: seq<uint8>,
    header: Header.Header,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<Frames.FinalFrame, string>)
    requires |key| == header.suite.encrypt.keyLength as nat
    requires START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires 0 <= |plaintext| < UINT32_LIMIT
    requires header.body.contentType.Framed?
    requires |plaintext| <= header.body.frameLength as nat
    ensures match res
      case Failure(e) => true
      case Success(frame) =>
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
        && frame.seqNum == sequenceNumber
        && frame.header == header
  {

    var iv := IVSeq(header.suite, sequenceNumber);

    var aad := BodyAAD(
      header.body.messageId,
      AADFinalFrame,
      sequenceNumber,
      |plaintext| as uint64
    );

    var encryptionOutput :- AESEncryption.AESEncrypt(
      header.suite.encrypt,
      iv,
      key,
      plaintext,
      aad
    );

    var finalFrame: Frames.FinalFrame := Frames.Frame.FinalFrame(
      header,
      sequenceNumber,
      iv,
      encryptionOutput.cipherText,
      encryptionOutput.authTag
    );

    return Success(finalFrame);
  }

  method DecryptFramedMessageBody(
    body: FramedMessage,
    key: seq<uint8>
  )
    returns (res: Result<seq<uint8>, string>)
    requires |key| == body.finalFrame.header.suite.encrypt.keyLength as int
    ensures match res
      case Failure(_) => true
      case Success(plaintext) => //Exists a sequence of frames which encrypts the plaintext and is serialized in the read section of the stream
        && FramesEncryptPlaintext(body, plaintext)
        && DecryptedWithKey(key, plaintext)
  {
    var plaintext := [];
    // var n: uint32 := 1;
    ghost var decryptedFrames: seq<Frames.RegularFrame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := []; // Chunks of plaintext which are decrypted from the frame

    for i := 0 to |body.regularFrames|
      invariant body.regularFrames[..i] == decryptedFrames
      // The goal is to assert FramesEncryptPlaintext.
      // But this requires the final frame e.g. a FramedMessage.
      // So I decompose this predicate into its parts
      invariant FramesEncryptPlaintextSegments(decryptedFrames, plaintextSeg) // So far: All decrypted frames decrypt to the list of plaintext chunks
      invariant SumPlaintextSegments(plaintextSeg) == plaintext // So far: The current plaintext is the sum of all decrypted chunks
      invariant DecryptedSegmentsWithKey(key, plaintextSeg)
      invariant DecryptedWithKey(key, plaintext)
    {

      var plaintextSegment :- DecryptFrame(body.regularFrames[i], key);

      plaintext := plaintext + plaintextSegment;
      plaintextSeg := plaintextSeg + [plaintextSegment];
      decryptedFrames := decryptedFrames + [body.regularFrames[i]];

      assert decryptedFrames[..i] == body.regularFrames[..i];
      assert decryptedFrames[..i] + [body.regularFrames[i]] == body.regularFrames[..i + 1];
    }
    var finalPlaintextSegment :- DecryptFrame(body.finalFrame, key);
    plaintext := plaintext + finalPlaintextSegment;
    plaintextSeg := plaintextSeg + [finalPlaintextSegment];

    assert FramesEncryptPlaintextSegments([body.finalFrame], [finalPlaintextSegment]);
    assert body.regularFrames == decryptedFrames;
    assert FramesEncryptPlaintextSegments(body.regularFrames + [body.finalFrame], plaintextSeg);
    assert SumPlaintextSegments(plaintextSeg) == plaintext;

    return Success(plaintext);
  }

  method DecryptFrame(
    frame: Frame,
    key: seq<uint8>
  )
    returns (res: Result<Uint8Seq32, string>)
    requires |key| == frame.header.suite.encrypt.keyLength as int
    ensures match res
      case Success(plaintextSegment) => ( // Decrypting the frame encoded in the stream is the returned ghost frame
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextSegment)
        && AESEncryption.DecryptedWithKey(key, plaintextSegment)
      )
      case Failure(_) => true
  {
    var aad := BodyAADForFrame(frame);

    var plaintextSegment :- AESEncryption.AESDecrypt(
      frame.header.suite.encrypt,
      key,
      frame.encContent,
      frame.authTag,
      frame.iv,
      aad
    );

    return Success(plaintextSegment);
  }

  method BodyAADForFrame(
    frame: Frame
  )
    returns (aad: seq<uint8>)
  {
    var (sequenceNumber, bc, length) := match frame
      case RegularFrame(header,seqNum,_,_,_) => (seqNum, AADRegularFrame, header.body.frameLength as uint64)
      case FinalFrame(_,seqNum,_, encContent,_) => (seqNum, AADFinalFrame, |encContent| as uint64)
      case NonFramed(_,_,encContent,_) => (NONFRAMED_SEQUENCE_NUMBER, AADSingleBlock, |encContent| as uint64);

    aad := BodyAAD(frame.header.body.messageId, bc, sequenceNumber, length);
  }

  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    aad := messageID + contentAAD.value + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  predicate DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)
  {
    if AESEncryption.DecryptedWithKey(key, plaintext) then true else
      exists plaintextSeg | SumPlaintextSegments(plaintextSeg) == plaintext ::
        DecryptedSegmentsWithKey(key, plaintextSeg)
  }

  predicate DecryptedSegmentsWithKey(key: seq<uint8>, plaintextSeg: seq<seq<uint8>>)
  {
    if plaintextSeg == [] then true else
      && DecryptedSegmentsWithKey(key, plaintextSeg[..|plaintextSeg| - 1])
      && AESEncryption.DecryptedWithKey(key, plaintextSeg[|plaintextSeg| - 1])
  }

  // method DecryptNonFramedMessageBody(
  //   rd: Streams.ByteReader,
  //   suite: Client.AlgorithmSuites.AlgorithmSuite,
  //   key: seq<uint8>,
  //   messageID: Msg.MessageID
  // )
  //   returns (res: Result<seq<uint8>, string>)
  //   requires rd.Valid()
  //   requires |key| == suite.encrypt.keyLength as int
  //   modifies rd.reader`pos
  //   ensures rd.Valid()
  // {
  //   var iv :- rd.ReadBytes(suite.encrypt.ivLength as int);
  //   var contentLength :- rd.ReadUInt64();
  //   var ciphertext :- rd.ReadBytes(contentLength as nat);
  //   var authTag :- rd.ReadBytes(suite.encrypt.tagLength as int);

  //   var aad := BodyAAD(messageID, AADSingleBlock, NONFRAMED_SEQUENCE_NUMBER, contentLength);

  //   var plaintext :- Decrypt(ciphertext, authTag, suite, iv, key, aad);
  //   return Success(plaintext);
  // }

  function method WriteFramedMessageBody(
    body: FramedMessage
  )
    :(ret: seq<uint8>)
    ensures ret == WriteMessageRegularFrames(body.regularFrames)
      + Frames.WriteFinalFrame(body.finalFrame)
  {
    WriteMessageRegularFrames(body.regularFrames) + Frames.WriteFinalFrame(body.finalFrame)
  }

  function method WriteMessageRegularFrames(
    frames: MessageRegularFrames
  )
    :(ret: seq<uint8>)
    ensures if |frames| == 0 then
      ret == []
    else
      ret == WriteMessageRegularFrames(Seq.DropLast(frames))
      + Frames.WriteRegularFrame(Seq.Last(frames))
  {
    if |frames| == 0 then []
    else
      WriteMessageRegularFrames(Seq.DropLast(frames))
      + Frames.WriteRegularFrame(Seq.Last(frames))
  }

  function method ReadFramedMessageBody(
    buffer: ReadableBuffer,
    header: Frames.FramedHeader,
    regularFrames: MessageRegularFrames,
    continuation: ReadableBuffer
  )
    :(res: ReadCorrect<FramedMessage>)
    requires forall frame: Frames.Frame
    | frame in regularFrames
    :: frame.header == header
    requires CorrectlyReadRange(buffer, continuation)
    requires CorrectlyRead(buffer, Success(SuccessfulRead(regularFrames, continuation)), WriteMessageRegularFrames)
    decreases ENDFRAME_SEQUENCE_NUMBER as nat - |regularFrames|
    ensures CorrectlyRead(buffer, res, WriteFramedMessageBody)
    ensures res.Success?
    ==>
      && res.value.data.finalFrame.header == header
  {
    var sequenceNumber :- ReadUInt32(continuation);
    if (sequenceNumber.data != ENDFRAME_SEQUENCE_NUMBER) then
      assert {:split_here} true;
      var regularFrame :- Frames.ReadRegularFrame(continuation, header);
      :- Need(regularFrame.data.seqNum as nat == |regularFrames| + 1, Error("Sequence number out of order."));

      assert {:split_here} true;
      LemmaAddingNextRegularFrame(regularFrames, regularFrame.data);

      var nextRegularFrames: MessageRegularFrames := regularFrames + [regularFrame.data];

      assert {:split_here} true;
      assert CorrectlyRead(continuation, Success(regularFrame), Frames.WriteRegularFrame);
      ghost var why? := [buffer, continuation, regularFrame.tail];
      assert {:split_here} true;
      ConsecutiveReadsAreAssociative(why?);

      assert {:split_here} true;
      ReadFramedMessageBody(
        buffer,
        header,
        nextRegularFrames,
        regularFrame.tail
      )
    else
      assert {:split_here} true;
      var finalFrame :- Frames.ReadFinalFrame(continuation, header);
      :- Need(finalFrame.data.seqNum as nat == |regularFrames| + 1, Error("Sequence number out of order."));

      assert {:split_here} true;
      assert MessageFramesAreMonotonic(regularFrames + [finalFrame.data]);
      assert MessageFramesAreForTheSameMessage(regularFrames + [finalFrame.data]);

      var body: FramedMessage := FramedMessageBody(
        regularFrames := regularFrames,
        finalFrame := finalFrame.data
      );

      assert {:split_here} true;
      assert CorrectlyRead(continuation, Success(finalFrame), Frames.WriteFinalFrame);
      ghost var why? := [buffer, continuation, finalFrame.tail];
      assert {:split_here} true;
      ConsecutiveReadsAreAssociative(why?);

      assert {:split_here} true;
      Success(SuccessfulRead(body, finalFrame.tail))
  }

  function WriteNonFramedMessageBody(
    body: NonFramedMessage
  )
    :(ret: seq<uint8>)
    ensures ret == Frames.WriteNonFramed(body)
  {
    Frames.WriteNonFramed(body)
  }

  function method ReadNonFramedMessageBody(
    buffer: ReadableBuffer,
    header: Frames.NonFramedHeader
  )
    :(res: ReadCorrect<NonFramedMessage>)
    ensures CorrectlyRead(buffer, res, WriteNonFramedMessageBody)
    ensures res.Success?
    ==>
      && res.value.data.header == header
  {
    var block :- Frames.ReadNonFrame(buffer, header);
    Success(SuccessfulRead(block.data, block.tail))
  }
}
