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

  // // Steps for inductive proofs EncryptMessageBody
  // lemma ExtendFramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>, frame: Frame, plaintextFrame: seq<uint8>)
  //   requires FramesEncryptPlaintextSegments(frames, plaintextSeg)
  //   requires AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextFrame)
  //   ensures FramesEncryptPlaintextSegments(frames + [frame], plaintextSeg + [plaintextFrame])
  // {
  // }

  function SumPlaintextSegments(plaintextSeg: seq<seq<uint8>>): seq<uint8>
  {
    if plaintextSeg == [] then
      []
    else
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg| - 1]) + plaintextSeg[|plaintextSeg| - 1]
  }

  // lemma ExtendSumPlaintextSegments(plaintextSeg: seq<seq<uint8>>, plaintextFrame: seq<uint8>)
  //   ensures SumPlaintextSegments(plaintextSeg + [plaintextFrame]) == SumPlaintextSegments(plaintextSeg) + plaintextFrame
  // {
  // }

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
        // var frames := seqWithGhostFrames.frames;
        // ValidFrames(frames)
        // && (forall frame | frame in frames :: frame.Valid())
        // && (forall frame: Frame | frame in frames :: |frame.iv| == suite.encrypt.ivLength as int)
        // && FramesToSequence(frames) == seqWithGhostFrames.sequence
        // && FramesEncryptPlaintext(body, plaintext)
        && (forall frame: Frames.RegularFrame
          | frame in body.regularFrames
          :: AESEncryption.EncryptedWithKey(frame.encContent, key))
        && AESEncryption.EncryptedWithKey(body.finalFrame.encContent, key)
  {
    // var body := [];
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    var regularFrames: MessageRegularFrames := [];
    // ghost var plaintextSeg := [];

    while n + header.body.frameLength as nat < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      // This needs to be inclusive
      // because this invariant MUST also be true when the loop exists.
      // If the final frame is going to be ENDFRAME_SEQUENCE_NUMBER,
      // then when this loop exists, sequenceNumber == ENDFRAME_SEQUENCE_NUMBER.
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant |regularFrames| == (sequenceNumber - START_SEQUENCE_NUMBER) as nat
      // invariant forall i // Sequence of frames is valid
      // | 0 <= i < |regularFrames|
      // ::
      //   && regularFrames[i].seqNum as nat == i + START_SEQUENCE_NUMBER as nat
      //   && regularFrames[i].header == header
      // invariant forall i | 0 <= i < |regularFrames| :: regularFrames[i].iv == IVSeq(suite, regularFrames[i].seqNum)
      // invariant FramesToSequence(regularFrames) == body
      // invariant FramesEncryptPlaintextSegments(regularFrames, plaintextSeg) // Frames decrypt to chunks of plaintext
      // invariant SumPlaintextSegments(plaintextSeg) == plaintext[..n] // Chunks of plaintext sum up to plaintexts
      invariant forall frame: Frames.RegularFrame
      | frame in regularFrames
      ::
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
        && frame.header == header
    {
      // assert {:split_here} true;
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

      // assert frame.iv == IVSeq(suite, sequenceNumber);
      // // Proofs that invariant holds after loop
      // ExtendFramesToSequence(frames, frame);
      // ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, frame, plaintextFrame);
      // ExtendSumPlaintextSegments(plaintextSeg, plaintextFrame);
      regularFrames := regularFrames + [regularFrame];
      // body := body + regularFrame.Extract();
      // plaintextSeg := plaintextSeg + [plaintextFrame];

      n, sequenceNumber := n + header.body.frameLength as nat, sequenceNumber + 1;
      // assert SumPlaintextSegments(plaintextSeg) == plaintext[..n];
    }
    // assert {:split_here} true;

    var finalFrame :- EncryptFinalFrame(
      key,
      header,
      plaintext[n..],
      sequenceNumber
    );

    // var finalFrameSequence := finalFrameResult.Extract();
    // assert finalFrame.iv == IVSeq(suite, sequenceNumber);
    // ExtendFramesToSequence(frames, finalFrame);
    // ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, finalFrame, plaintext[n..]);
    // ExtendSumPlaintextSegments(plaintextSeg, plaintext[n..]);
    // var frames := regularFrames + [finalFrame];
    // body := body + finalFrameSequence;
    // plaintextSeg := plaintextSeg + [plaintext[n..]];
    // assert ValidFrames(frames) by {
    //   forall i,j | 0 <= i < j < |frames|
    //     ensures frames[i].iv != frames[j].iv
    //   {
    //     assert frames[i].seqNum as int == i + START_SEQUENCE_NUMBER as int;
    //     assert frames[j].seqNum as int == j + START_SEQUENCE_NUMBER as int;
    //     assert frames[i].iv == IVSeq(suite, frames[i].seqNum);
    //     assert frames[j].iv == IVSeq(suite, frames[j].seqNum);
    //     IVSeqDistinct(suite, frames[i].seqNum, frames[j].seqNum);
    //   }
    // }

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
    // Why is this require here? ivLength is 12, not ever 4-11. ?
    // requires 4 <= suite.encrypt.ivLength as int
    ensures match res
      case Failure(e) => true
      case Success(frame) =>
        //    // Decrypt serialized frame back to frame and state that it is equal to the ghost frame
        // 4 + suite.encrypt.ivLength as int + suite.encrypt.tagLength as int + frameLength == |resultSuccess|
        // && var iv := IVSeq(suite, sequenceNumber);
        // var encContent := resultSuccess[4 + suite.encrypt.ivLength as int..4 + suite.encrypt.ivLength as int + frameLength];
        // var authTag := resultSuccess[4 + suite.encrypt.ivLength as int + frameLength..];
        // var frame := RegularFrame(sequenceNumber, iv, encContent, authTag);
        // frame == regFrame
        // && FrameToSequence(regFrame) == resultSuccess
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

    // SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    // unauthenticatedFrame := unauthenticatedFrame + iv;
    // unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

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
    // requires 0 < header.body.frameLength as nat < UINT32_LIMIT
    requires header.body.contentType.Framed?
    requires |plaintext| <= header.body.frameLength as nat
    // requires 4 <= header.suite.encrypt.ivLength as int
    ensures match res
      case Failure(e) => true
      case Success(frame) =>
        // // Decrypt serialized frame back to frame and state that it is equal to the ghost frame
        // 4 + 4 + suite.encrypt.ivLength as int + 4 + suite.encrypt.tagLength as int <= |resultSuccess|
        //   <= 4 + 4 + suite.encrypt.ivLength as int + 4 + suite.encrypt.tagLength as int + frameLength
        // && var contentLength : uint32 := SeqToUInt32(resultSuccess[4+4+suite.encrypt.ivLength as int..4+4+suite.encrypt.ivLength as int+4]);
        // |resultSuccess| == 4 + 4 + suite.encrypt.ivLength as int + 4 + contentLength as int + suite.encrypt.tagLength as int
        // && resultSuccess[..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
        // && |plaintext| == SeqToUInt32(resultSuccess[4 + 4 + suite.encrypt.ivLength as int..4 + 4 + suite.encrypt.ivLength as int + 4]) as int &&
        // var iv := IVSeq(suite, sequenceNumber);
        // var encContent := resultSuccess[4 + 4 + suite.encrypt.ivLength as int + 4..][..|plaintext|];
        // var authTag := resultSuccess[4 + 4 + suite.encrypt.ivLength as int + 4 + |plaintext|..];
        // var frame := FinalFrame(sequenceNumber, iv, encContent, authTag);
        // FrameToSequence(frame) == resultSuccess
        // && finalFrame == frame
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
        && frame.seqNum == sequenceNumber
        && frame.header == header
  {
    // var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    // var seqNumSeq := UInt32ToSeq(sequenceNumber);
    // unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;

    var iv := IVSeq(header.suite, sequenceNumber);
    // SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    // unauthenticatedFrame := unauthenticatedFrame + iv;
    // unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);

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

    // var encryptionOutput := encryptionOutputResult.Extract();
    // unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    // assert |plaintext| == |encryptionOutput.cipherText|;

    // ghost var frame := FinalFrame(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    // finalFrame := frame;
    // assert FrameToSequence(frame) == unauthenticatedFrame;
    // // Show which part of the serialized frame map to which frame variable
    // assert |plaintext| == SeqToUInt32(unauthenticatedFrame[4 + 4 + suite.encrypt.ivLength as int..4 + 4 + suite.encrypt.ivLength as int + 4]) as int;
    // assert |unauthenticatedFrame| == 4 + 4 + suite.encrypt.ivLength as int + 4 + |plaintext| + suite.encrypt.tagLength as int;
    // assert unauthenticatedFrame[4 + 4 + suite.encrypt.ivLength as int + 4..][..|plaintext|] == encryptionOutput.cipherText;

    return Success(finalFrame);
  }

  method DecryptFramedMessageBody(
    body: FramedMessage,
    key: seq<uint8>
  )
    returns (res: Result<seq<uint8>, string>)
    // requires rd.Valid()
    requires |key| == body.finalFrame.header.suite.encrypt.keyLength as int
    // requires 0 < frameLength < UINT32_LIMIT
    // modifies rd.reader`pos
    // ensures rd.Valid()
    // ensures res.Success? ==> DecryptedWithKey(key, res.value)
    ensures match res
      case Failure(_) => true
      case Success(plaintext) => //Exists a sequence of frames which encrypts the plaintext and is serialized in the read section of the stream
        // old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
        // && exists frames: seq<Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid())
        //     && FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos] ::
        //       && FramesEncryptPlaintext(frames, plaintext)
        && FramesEncryptPlaintext(body, plaintext)
        && DecryptedWithKey(key, plaintext)
  {
    var plaintext := [];
    // var n: uint32 := 1;
    ghost var decryptedFrames: seq<Frames.RegularFrame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := []; // Chuncks of plaintext which are decrypted from the frame

    // while true
    //   decreases ENDFRAME_SEQUENCE_NUMBER - n
    //   invariant rd.Valid()
    //   invariant n as int - 1 == |frames|
    //   invariant n <= ENDFRAME_SEQUENCE_NUMBER
    //   invariant forall frame | frame in frames :: frame.Valid()
    //   invariant old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
    //   invariant FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
    //   invariant rd.Valid()
    //   invariant FramesEncryptPlaintextSegments(frames, plaintextSeg) // All decrypted frames decrypt to the list of plaintext chuncks
    //   invariant SumPlaintextSegments(plaintextSeg) == plaintext // The current decrypted frame is the sum of all decrypted chuncks
    //   invariant DecryptedSegmentsWithKey(key, plaintextSeg)
    //   invariant plaintext == SumPlaintextSegments(plaintextSeg)
    // {
    //   // assert {:split_here} true;
    //   var frameWithGhostSeq :- DecryptFrame(rd, suite, key, frameLength, messageID, n);
    //   assert |frameWithGhostSeq.sequence| < UINT32_LIMIT;
    //   var decryptedFrame := frameWithGhostSeq.frame;
    //   ghost var ciphertext := frameWithGhostSeq.sequence;
    //   assert |ciphertext| < UINT32_LIMIT;
    //   ghost var encryptedFrame := if decryptedFrame.FinalFrame? then
    //     FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
    //   else
    //     RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag);
    //   assert encryptedFrame.Valid();
    //   frames := frames + [encryptedFrame];

    //   var (decryptedFramePlaintext, final) := (decryptedFrame.encContent, decryptedFrame.FinalFrame?);
    //   plaintext := plaintext + decryptedFramePlaintext;
    //   plaintextSeg := plaintextSeg + [decryptedFramePlaintext];
    //   if final {
    //     assert FramesEncryptPlaintextSegments(frames, plaintextSeg);
    //     assert SumPlaintextSegments(plaintextSeg) == plaintext;
    //     break;
    //   }

    //   n := n + 1;
    // }

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

      assert decryptedFrames[..i] + [body.regularFrames[i]] == body.regularFrames[..i + 1];
    }
    var finalPlaintextSegment :- DecryptFrame(body.finalFrame, key);
    plaintext := plaintext + finalPlaintextSegment;
    plaintextSeg := plaintextSeg + [finalPlaintextSegment];

    // assert FramesEncryptPlaintextSegments(decryptedFrames, plaintextSeg);
    assert FramesEncryptPlaintextSegments([body.finalFrame], [finalPlaintextSegment]);
    assert body.regularFrames == decryptedFrames;
    assert FramesEncryptPlaintextSegments(body.regularFrames + [body.finalFrame], plaintextSeg);
    assert SumPlaintextSegments(plaintextSeg) == plaintext;

    // assert |frames| < UINT32_LIMIT ;
    // assert (forall frame | frame in frames :: frame.Valid()) ;
    // assert FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos];
    return Success(plaintext);
  }

  method DecryptFrame(
    frame: Frame,
    key: seq<uint8>
    // ,expectedSequenceNumber: uint32
  )
    returns (res: Result<Uint8Seq32, string>)
    // requires rd.Valid()
    requires |key| == frame.header.suite.encrypt.keyLength as int
    // requires 0 < frameLength < UINT32_LIMIT
    // modifies rd.reader`pos
    // ensures rd.Valid()
    // ensures match res // If the expected sequence number is the end frame sequence number then the frame is the final frame. However, the final frame can arrive earlier
    //   case Success(frameWithGhostSeq) =>
    //     expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> frameWithGhostSeq.frame.FinalFrame?
    //   case Failure(_) => true
    // ensures res.Success? ==> |res.value| < UINT32_LIMIT
    ensures match res
      case Success(plaintextSegment) => ( // Decrypting the frame encoded in the stream is the returned ghost frame
        // && var decryptedFrame := frameWithGhostSeq.frame;
        //    var ciphertext := frameWithGhostSeq.sequence;
        //    var final := decryptedFrame.FinalFrame?;
        //    decryptedFrame.Valid()
        // && old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextSegment)
        && AESEncryption.DecryptedWithKey(key, plaintextSegment)
      //   && var encryptedFrame := (if decryptedFrame.FinalFrame? then
      //        FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
      //      else
      //        RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag));
      //      rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == FrameToSequence(encryptedFrame)
      //   && AESEncryption.CiphertextGeneratedWithPlaintext(encryptedFrame.encContent, decryptedFrame.encContent)
      )
      case Failure(_) => true
  {
    // var final := false;
    // var sequenceNumber :- rd.ReadUInt32();
    // ghost var frameSerialization := UInt32ToSeq(sequenceNumber);
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    // if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
    //   final := true;
    //   sequenceNumber :- rd.ReadUInt32();
    //   frameSerialization := frameSerialization + UInt32ToSeq(sequenceNumber);
    //   assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;
    // }

    // if sequenceNumber != expectedSequenceNumber {
    //   return Failure("unexpected frame sequence number");
    // }

    // assert {:focus} true;
    // var iv :- rd.ReadBytes(suite.encrypt.ivLength as int);
    // frameSerialization := frameSerialization + iv;
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    // var len := frameLength as uint32;
    // if final {
    //   len :- rd.ReadUInt32();
    //   if len > frameLength as uint32 {
    //     return Failure("Final frame too long");
    //   }
    //   frameSerialization := frameSerialization + UInt32ToSeq(len);
    // }

    var aad := BodyAADForFrame(frame);

    // assert {:focus} true;
    // var ciphertext :- rd.ReadBytes(len as nat);
    // frameSerialization := frameSerialization + ciphertext;
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    // var authTag :- rd.ReadBytes(suite.encrypt.tagLength as int);
    // frameSerialization := frameSerialization + authTag;
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    var plaintextSegment :- AESEncryption.AESDecrypt(
      frame.header.suite.encrypt,
      key,
      frame.encContent,
      frame.authTag,
      frame.iv,
      aad
    );

    // assert AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, plaintext);
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    // var frame := if final then
    //     FinalFrame(sequenceNumber, iv, plaintext, authTag)
    //   else
    //     RegularFrame(sequenceNumber, iv, plaintext, authTag);

    // ghost var encryptedFrame := if final then
    //     FinalFrame(sequenceNumber, iv, ciphertext, authTag)
    //   else
    //     RegularFrame(sequenceNumber, iv, ciphertext, authTag);

    // // Feed dafny facts about the content of the stream
    // // Show dafny that the serialized frame is frameSerialization
    // assert frameSerialization == FrameToSequence(encryptedFrame);

    // // Prove read content of stream is frameSerialization
    // assert {:focus} true;
    // assert !final ==> frameSerialization[..4] == rd.reader.data[old(rd.reader.pos)..][..4];
    // assert !final ==> frameSerialization[4..][..suite.encrypt.ivLength as int] == rd.reader.data[old(rd.reader.pos)..][4..][..suite.encrypt.ivLength as int];
    // assert !final ==> frameSerialization[4 + suite.encrypt.ivLength as int..][..frameLength] == rd.reader.data[old(rd.reader.pos)..][4 + suite.encrypt.ivLength as int..][..frameLength];
    // assert !final ==> frameSerialization[4 + frameLength + suite.encrypt.ivLength as int..] == rd.reader.data[old(rd.reader.pos)..][4 + frameLength + suite.encrypt.ivLength as int..][..suite.encrypt.tagLength as int];

    // // Prove equivalence frameSerialization and content read on the stream
    // assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    // assert old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|;

    // return Success(FrameWithGhostSeq(frame,ciphertext));
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

  // method Decrypt(
  //   ciphertext: seq<uint8>,
  //   authTag: seq<uint8>,
  //   suite: Client.AlgorithmSuites.AlgorithmSuite,
  //   iv: seq<uint8>,
  //   key: seq<uint8>,
  //   aad: seq<uint8>
  // )
  //   returns (res: Result<seq<uint8>, string>)
  //   requires
  //     && |iv| == suite.encrypt.ivLength as int
  //     && |key| == suite.encrypt.keyLength as int
  //     && |authTag| == suite.encrypt.tagLength as int
  //   ensures res.Success? ==> AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, res.value)
  //   ensures res.Success? ==> |ciphertext| == |res.value|
  //   ensures res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value)
  // {
  //   var encAlg := suite.encrypt;
  //   res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
  //   assert res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value);
  // }

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
    bytes: ReadableBytes,
    header: Frames.FramedHeader,
    regularFrames: MessageRegularFrames,
    continuation: ReadableBytes
  )
    :(res: ReadCorrect<FramedMessage>)
    requires forall frame: Frames.RegularFrame
    | frame in regularFrames
    :: frame.header == header
    requires CorrectlyRead(bytes, Success(Data(regularFrames, continuation)), WriteMessageRegularFrames)
    decreases ENDFRAME_SEQUENCE_NUMBER as nat - |regularFrames|
    ensures CorrectlyRead(bytes, res, WriteFramedMessageBody)
  {
    var sequenceNumber :- ReadUInt32(continuation);
    if (sequenceNumber.thing != ENDFRAME_SEQUENCE_NUMBER) then
      var regularFrame :- Frames.ReadRegularFrame(continuation, header);
      :- Need(regularFrame.thing.seqNum as nat == |regularFrames| + 1, Error("Sequence number out of order."));
      LemmaAddingNextRegularFrame(regularFrames, regularFrame.thing);
      var nextRegularFrames: MessageRegularFrames := regularFrames + [regularFrame.thing];
      ReadableBytesStartPositionsAreAssociative(bytes, continuation, regularFrame.tail);
      ReadFramedMessageBody(
        bytes,
        header,
        nextRegularFrames,
        regularFrame.tail
      )
    else
      var finalFrame :- Frames.ReadFinalFrame(continuation, header);
      :- Need(finalFrame.thing.seqNum as nat == |regularFrames| + 1, Error("Sequence number out of order."));
      ReadableBytesStartPositionsAreAssociative(bytes, continuation, finalFrame.tail);
      assert MessageFramesAreMonotonic(regularFrames + [finalFrame.thing]);
      assert MessageFramesAreForTheSameMessage(regularFrames + [finalFrame.thing]);
      var body: FramedMessage := FramedMessageBody(
        regularFrames := regularFrames,
        finalFrame := finalFrame.thing
      );
      
      Success(Data(body, finalFrame.tail))
  }
}
