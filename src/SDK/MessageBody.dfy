// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "MessageHeader.dfy"
include "Serialize/SerializableTypes.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Util/Streams.dfy"
include "../Util/UTF8.dfy"

module MessageBody {
  export
    provides EncryptMessageBody, DecryptFramedMessageBody, DecryptNonFramedMessageBody,
      Wrappers, UInt, Msg, Streams, FramesToSequence, Client,
      FrameToSequence, ValidFrames, FramesEncryptPlaintext, AESEncryption, DecryptedWithKey
    reveals Frame, Frame.Valid, SeqWithGhostFrames

  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Msg = MessageHeader
  import AESEncryption
  import Streams
  import UTF8
  import SerializableTypes
  import MaterialProviders.Client

  datatype BodyAADContent = AADRegularFrame | AADFinalFrame | AADSingleBlock

  /**
    The behavior of the methods in this file are specified in https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/data-format/message-body.md
    The Frame datatype has been introduced in the validation of this file. This datatype is only used for the validation.
    The methods in this file serialize and deserialize some plaintext to frames. Frame are encoded in a sequence of bytes.
  */

  // Predicate all conditions which should hold for any valid sequence of frames
  predicate ValidFrames(frames: seq<Frame>) {
    0 < |frames| < UINT32_LIMIT &&
    forall i | 0 <= i < |frames| ::
      var frame := frames[i];
      frame.Valid() &&
      (if i == |frames| - 1 then frame.FinalFrame? else frame.RegularFrame?) &&
      frame.seqNum as int == i + START_SEQUENCE_NUMBER as int &&
      (forall j | i < j < |frames| :: frame.iv != frames[j].iv)
  }

  datatype Frame = RegularFrame(seqNum: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) |
                   FinalFrame(seqNum: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>)
  {
    predicate Valid() {
      |encContent| < UINT32_LIMIT
    }
  }

  const BODY_AAD_CONTENT_REGULAR_FRAME: string := "AWSKMSEncryptionClient Frame"
  const BODY_AAD_CONTENT_FINAL_FRAME: string := "AWSKMSEncryptionClient Final Frame"
  const BODY_AAD_CONTENT_SINGLE_BLOCK: string := "AWSKMSEncryptionClient Single Block"

  function method BodyAADContentTypeString(bc: BodyAADContent): string {
    match bc
    case AADRegularFrame => BODY_AAD_CONTENT_REGULAR_FRAME
    case AADFinalFrame => BODY_AAD_CONTENT_FINAL_FRAME
    case AADSingleBlock => BODY_AAD_CONTENT_SINGLE_BLOCK
  }

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := 1

  function method IVSeq(suite: Client.AlgorithmSuites.AlgorithmSuite, sequenceNumber: uint32): seq<uint8> {
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

  // Converts sequence of Frames to a sequence encoding all frames
  function FramesToSequence(frames : seq<Frame>): seq<uint8>
    requires forall frame | frame in frames :: frame.Valid()
  {
    if frames == [] then
      []
    else
      FramesToSequence(frames[..|frames| - 1]) + FrameToSequence(frames[|frames| - 1])
  }

  lemma ExtendFramesToSequence(frames: seq<Frame>, frame: Frame)
    requires |frames| < UINT32_LIMIT - 1
    requires forall frame | frame in frames :: frame.Valid()
    requires frame.Valid()
    ensures FramesToSequence(frames + [frame]) == FramesToSequence(frames) + FrameToSequence(frame)
  {
  }

  // Converts Frame to a sequence encoding a frame
  function FrameToSequence(frame: Frame): (res: seq<uint8>)
    requires frame.Valid()
    ensures match frame
      case RegularFrame(_, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) =>
        4 + |iv| + |encContent| + |authTag| == |res|
      case FinalFrame(seqNum: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) =>
        4 + 4 + |iv| + 4 + |encContent| + |authTag| == |res|
  {
    match frame
      case RegularFrame(seqNum, iv, encContent, authTag) =>
        var seqNumSeq := UInt32ToSeq(seqNum);
        seqNumSeq + iv + encContent + authTag
      case FinalFrame(seqNum, iv, encContent, authTag) =>
        var seqNumEndSeq := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
        var seqNumSeq := UInt32ToSeq(seqNum);
        var encContentLengthSeq := UInt32ToSeq(|encContent| as uint32);
        seqNumEndSeq + seqNumSeq + iv + encContentLengthSeq + encContent + authTag
  }

  /**
    Predicate states that frames encrypt plaintext

      Plaintext is split into chunks of frameLength. One chunck is encrypted in one frame. Reasoning about chunks makes proving predicate easier
        FramesEncryptPlaintextSegments: States that sequence of frames decrypts to sequence of chunks
        SumPlaintextSegments: States that sum of chunks is the plaintext
   */
  predicate FramesEncryptPlaintext(frames: seq<Frame>, plaintext: seq<uint8>)
  {
    exists plaintextSeg: seq<seq<uint8>> ::
      FramesEncryptPlaintextSegments(frames, plaintextSeg) && SumPlaintextSegments(plaintextSeg) == plaintext
  }

  predicate FramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>)
  {
    if |frames| != |plaintextSeg| then
      false
    else
      if frames == [] then
        true
      else
        FramesEncryptPlaintextSegments(frames[..|frames| - 1], plaintextSeg[..|frames| - 1]) &&
        AESEncryption.CiphertextGeneratedWithPlaintext(frames[|frames| - 1].encContent, plaintextSeg[|frames| - 1])
  }

  // Steps for inductive proofs EncryptMessageBody
  lemma ExtendFramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>, frame: Frame, plaintextFrame: seq<uint8>)
    requires FramesEncryptPlaintextSegments(frames, plaintextSeg)
    requires AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextFrame)
    ensures FramesEncryptPlaintextSegments(frames + [frame], plaintextSeg + [plaintextFrame])
  {
  }

  function SumPlaintextSegments(plaintextSeg: seq<seq<uint8>>): seq<uint8>
  {
    if plaintextSeg == [] then
      []
    else
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg| - 1]) + plaintextSeg[|plaintextSeg| - 1]
  }

  lemma ExtendSumPlaintextSegments(plaintextSeg: seq<seq<uint8>>, plaintextFrame: seq<uint8>)
    ensures SumPlaintextSegments(plaintextSeg + [plaintextFrame]) == SumPlaintextSegments(plaintextSeg) + plaintextFrame
  {
  }

  datatype SeqWithGhostFrames = SeqWithGhostFrames(sequence: seq<uint8>, ghost frames: seq<Frame>)

  method EncryptMessageBody(
    plaintext: seq<uint8>,
    frameLength: int,
    messageID: Msg.MessageID,
    key: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    returns (result: Result<SeqWithGhostFrames, string>)
    requires |key| ==  suite.encrypt.keyLength as int
    requires 0 < frameLength < UINT32_LIMIT
    ensures match result
      case Failure(e) => true
      case Success(seqWithGhostFrames) =>
        var frames := seqWithGhostFrames.frames;
        ValidFrames(frames)
        && (forall frame | frame in frames :: frame.Valid())
        && (forall frame: Frame | frame in frames :: |frame.iv| == suite.encrypt.ivLength as int)
        && FramesToSequence(frames) == seqWithGhostFrames.sequence
        && FramesEncryptPlaintext(frames, plaintext)
        && (forall frame: Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, key))
  {
    var body := [];
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    ghost var frames : seq<Frame> := [];
    ghost var plaintextSeg := [];

    while n + frameLength < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant |frames| == (sequenceNumber - START_SEQUENCE_NUMBER) as int
      invariant forall i | 0 <= i < |frames| :: // Sequence of frames is valid
        var frame := frames[i];
        frame.Valid() &&
        frame.RegularFrame? &&
        frame.seqNum as int == i + START_SEQUENCE_NUMBER as int
      invariant forall i | 0 <= i < |frames| :: frames[i].iv == IVSeq(suite, frames[i].seqNum)
      invariant FramesToSequence(frames) == body
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg) // Frames decrypt to chunks of plaintext
      invariant SumPlaintextSegments(plaintextSeg) == plaintext[..n] // Chunks of plaintext sum up to plaintexts
      invariant forall frame: Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, key)
    {
      assert {:split_here} true;
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure("too many frames");
      }
      var plaintextFrame := plaintext[n..n + frameLength];
      var regularFrame, frame := EncryptRegularFrame(suite, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      if regularFrame.IsFailure() {
        return regularFrame.PropagateFailure();
      }
      assert frame.iv == IVSeq(suite, sequenceNumber);

      // Proofs that invariant holds after loop
      ExtendFramesToSequence(frames, frame);
      ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, frame, plaintextFrame);
      ExtendSumPlaintextSegments(plaintextSeg, plaintextFrame);
      frames := frames + [frame];
      body := body + regularFrame.Extract();
      plaintextSeg := plaintextSeg + [plaintextFrame];

      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
      assert SumPlaintextSegments(plaintextSeg) == plaintext[..n];
    }
    assert {:split_here} true;

    var finalFrameResult, finalFrame := EncryptFinalFrame(suite, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    if finalFrameResult.IsFailure() {
      return finalFrameResult.PropagateFailure();
    }
    var finalFrameSequence := finalFrameResult.Extract();
    assert finalFrame.iv == IVSeq(suite, sequenceNumber);
    ExtendFramesToSequence(frames, finalFrame);
    ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, finalFrame, plaintext[n..]);
    ExtendSumPlaintextSegments(plaintextSeg, plaintext[n..]);
    frames := frames + [finalFrame];
    body := body + finalFrameSequence;
    plaintextSeg := plaintextSeg + [plaintext[n..]];
    assert ValidFrames(frames) by {
      forall i,j | 0 <= i < j < |frames|
        ensures frames[i].iv != frames[j].iv
      {
        assert frames[i].seqNum as int == i + START_SEQUENCE_NUMBER as int;
        assert frames[j].seqNum as int == j + START_SEQUENCE_NUMBER as int;
        assert frames[i].iv == IVSeq(suite, frames[i].seqNum);
        assert frames[j].iv == IVSeq(suite, frames[j].seqNum);
        IVSeqDistinct(suite, frames[i].seqNum, frames[j].seqNum);
      }
    }

    result := Success(SeqWithGhostFrames(body, frames));
  }

  method EncryptRegularFrame(
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    key: seq<uint8>,
    ghost frameLength: int,
    messageID: Msg.MessageID,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<seq<uint8>, string>, ghost regFrame: Frame)
    requires |key| == suite.encrypt.keyLength as int
    requires 0 < frameLength < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    // Why is this require here? ivLength is 12, not ever 4-11. ?
    // requires 4 <= suite.encrypt.ivLength as int
    ensures match res
      case Failure(e) => true
      case Success(resultSuccess) =>
           // Decrypt serialized frame back to frame and state that it is equal to the ghost frame
        4 + suite.encrypt.ivLength as int + suite.encrypt.tagLength as int + frameLength == |resultSuccess|
        && var iv := IVSeq(suite, sequenceNumber);
        var encContent := resultSuccess[4 + suite.encrypt.ivLength as int..4 + suite.encrypt.ivLength as int + frameLength];
        var authTag := resultSuccess[4 + suite.encrypt.ivLength as int + frameLength..];
        var frame := RegularFrame(sequenceNumber, iv, encContent, authTag);
        frame == regFrame
        && FrameToSequence(regFrame) == resultSuccess
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := IVSeq(suite, sequenceNumber);
    var aad := BodyAAD(messageID, AADRegularFrame, sequenceNumber, |plaintext| as uint64);

    var encryptionOutputResult := AESEncryption.AESEncrypt(suite.encrypt, iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      regFrame := RegularFrame(0, [], [], []); // irrelevant value supplied for the sake of determinism
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    ghost var frame := RegularFrame(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);

    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

    return Success(unauthenticatedFrame), frame;
  }

  method EncryptFinalFrame(
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    key: seq<uint8>,
    frameLength: int,
    messageID: Msg.MessageID,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<seq<uint8>, string>, ghost finalFrame: Frame)
    requires |key| == suite.encrypt.keyLength as int
    requires START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires 0 <= |plaintext| < UINT32_LIMIT
    requires 0 < frameLength < UINT32_LIMIT
    requires |plaintext| <= frameLength
    requires 4 <= suite.encrypt.ivLength as int
    ensures match res
      case Failure(e) => true
      case Success(resultSuccess) =>
        // Decrypt serialized frame back to frame and state that it is equal to the ghost frame
        4 + 4 + suite.encrypt.ivLength as int + 4 + suite.encrypt.tagLength as int <= |resultSuccess|
          <= 4 + 4 + suite.encrypt.ivLength as int + 4 + suite.encrypt.tagLength as int + frameLength
        && var contentLength : uint32 := SeqToUInt32(resultSuccess[4+4+suite.encrypt.ivLength as int..4+4+suite.encrypt.ivLength as int+4]);
        |resultSuccess| == 4 + 4 + suite.encrypt.ivLength as int + 4 + contentLength as int + suite.encrypt.tagLength as int
        && resultSuccess[..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
        && |plaintext| == SeqToUInt32(resultSuccess[4 + 4 + suite.encrypt.ivLength as int..4 + 4 + suite.encrypt.ivLength as int + 4]) as int &&
        var iv := IVSeq(suite, sequenceNumber);
        var encContent := resultSuccess[4 + 4 + suite.encrypt.ivLength as int + 4..][..|plaintext|];
        var authTag := resultSuccess[4 + 4 + suite.encrypt.ivLength as int + 4 + |plaintext|..];
        var frame := FinalFrame(sequenceNumber, iv, encContent, authTag);
        FrameToSequence(frame) == resultSuccess
        && finalFrame == frame
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
        && AESEncryption.EncryptedWithKey(frame.encContent, key)
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;

    var iv := IVSeq(suite, sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);

    var aad := BodyAAD(messageID, AADFinalFrame, sequenceNumber, |plaintext| as uint64);

    var encryptionOutputResult := AESEncryption.AESEncrypt(suite.encrypt, iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      finalFrame := RegularFrame(0, [], [], []); // irrelevant value supplied for the sake of determinism
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    assert |plaintext| == |encryptionOutput.cipherText|;

    ghost var frame := FinalFrame(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    finalFrame := frame;
    assert FrameToSequence(frame) == unauthenticatedFrame;
    // Show which part of the serialized frame map to which frame variable
    assert |plaintext| == SeqToUInt32(unauthenticatedFrame[4 + 4 + suite.encrypt.ivLength as int..4 + 4 + suite.encrypt.ivLength as int + 4]) as int;
    assert |unauthenticatedFrame| == 4 + 4 + suite.encrypt.ivLength as int + 4 + |plaintext| + suite.encrypt.tagLength as int;
    assert unauthenticatedFrame[4 + 4 + suite.encrypt.ivLength as int + 4..][..|plaintext|] == encryptionOutput.cipherText;

    return Success(unauthenticatedFrame), finalFrame;
  }

  method DecryptFramedMessageBody(
    rd: Streams.ByteReader,
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    key: seq<uint8>,
    frameLength: int,
    messageID: Msg.MessageID
  )
    returns (res: Result<seq<uint8>, string>)
    requires rd.Valid()
    requires |key| == suite.encrypt.keyLength as int
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    ensures match res
      case Failure(_) => true
      case Success(plaintext) => //Exists a sequence of frames which encrypts the plaintext and is serialized in the read section of the stream
        old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
        && exists frames: seq<Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid())
            && FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos] ::
              && FramesEncryptPlaintext(frames, plaintext)
  {
    var plaintext := [];
    var n: uint32 := 1;
    ghost var frames: seq<Frame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := []; // Chuncks of plaintext which are decrypted from the frame

    while true
      decreases ENDFRAME_SEQUENCE_NUMBER - n
      invariant rd.Valid()
      invariant n as int - 1 == |frames|
      invariant n <= ENDFRAME_SEQUENCE_NUMBER
      invariant forall frame | frame in frames :: frame.Valid()
      invariant old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
      invariant FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      invariant rd.Valid()
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg) // All decrypted frames decrypt to the list of plaintext chuncks
      invariant SumPlaintextSegments(plaintextSeg) == plaintext // The current decrypted frame is the sum of all decrypted chuncks
      invariant DecryptedSegmentsWithKey(key, plaintextSeg)
      invariant plaintext == SumPlaintextSegments(plaintextSeg)
    {
      assert {:split_here} true;
      var frameWithGhostSeq :- DecryptFrame(rd, suite, key, frameLength, messageID, n);
      assert |frameWithGhostSeq.sequence| < UINT32_LIMIT;
      var decryptedFrame := frameWithGhostSeq.frame;
      ghost var ciphertext := frameWithGhostSeq.sequence;
      assert |ciphertext| < UINT32_LIMIT;
      ghost var encryptedFrame := if decryptedFrame.FinalFrame? then
        FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
      else
        RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag);
      assert encryptedFrame.Valid();
      frames := frames + [encryptedFrame];

      var (decryptedFramePlaintext, final) := (decryptedFrame.encContent, decryptedFrame.FinalFrame?);
      plaintext := plaintext + decryptedFramePlaintext;
      plaintextSeg := plaintextSeg + [decryptedFramePlaintext];
      if final {
        assert FramesEncryptPlaintextSegments(frames, plaintextSeg);
        assert SumPlaintextSegments(plaintextSeg) == plaintext;
        break;
      }

      n := n + 1;
    }
    assert |frames| < UINT32_LIMIT ;
    assert (forall frame | frame in frames :: frame.Valid()) ;
    assert FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos];
    return Success(plaintext);
  }

  datatype FrameWithGhostSeq = FrameWithGhostSeq(frame: Frame, ghost sequence: seq<uint8>)

  method DecryptFrame(
    rd: Streams.ByteReader,
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    key: seq<uint8>,
    frameLength: int,
    messageID: Msg.MessageID,
    expectedSequenceNumber: uint32
  )
    returns (res: Result<FrameWithGhostSeq, string>)
    requires rd.Valid()
    requires |key| == suite.encrypt.keyLength as int
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res // If the expected sequence number is the end frame sequence number then the frame is the final frame. However, the final frame can arrive earlier
      case Success(frameWithGhostSeq) =>
        expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> frameWithGhostSeq.frame.FinalFrame?
      case Failure(_) => true
    ensures res.Success? ==> |res.value.sequence| < UINT32_LIMIT
    ensures match res
      case Success(frameWithGhostSeq) => ( // Decrypting the frame encoded in the stream is the returned ghost frame
        && var decryptedFrame := frameWithGhostSeq.frame;
           var ciphertext := frameWithGhostSeq.sequence;
           var final := decryptedFrame.FinalFrame?;
           decryptedFrame.Valid()
        && old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|
        && AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, decryptedFrame.encContent)
        && AESEncryption.DecryptedWithKey(key, decryptedFrame.encContent)
        && var encryptedFrame := (if decryptedFrame.FinalFrame? then
             FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
           else
             RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag));
           rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == FrameToSequence(encryptedFrame)
        && AESEncryption.CiphertextGeneratedWithPlaintext(encryptedFrame.encContent, decryptedFrame.encContent))
      case Failure(_) => true
  {
    var final := false;
    var sequenceNumber :- rd.ReadUInt32();
    ghost var frameSerialization := UInt32ToSeq(sequenceNumber);
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
      frameSerialization := frameSerialization + UInt32ToSeq(sequenceNumber);
      assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;
    }

    if sequenceNumber != expectedSequenceNumber {
      return Failure("unexpected frame sequence number");
    }

    assert {:focus} true;
    var iv :- rd.ReadBytes(suite.encrypt.ivLength as int);
    frameSerialization := frameSerialization + iv;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
      if len > frameLength as uint32 {
        return Failure("Final frame too long");
      }
      frameSerialization := frameSerialization + UInt32ToSeq(len);
    }

    var aad := BodyAAD(messageID, if final then AADFinalFrame else AADRegularFrame, sequenceNumber, len as uint64);

    assert {:focus} true;
    var ciphertext :- rd.ReadBytes(len as nat);
    frameSerialization := frameSerialization + ciphertext;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    var authTag :- rd.ReadBytes(suite.encrypt.tagLength as int);
    frameSerialization := frameSerialization + authTag;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    var plaintext :- Decrypt(ciphertext, authTag, suite, iv, key, aad);
    assert AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, plaintext);
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    var frame := if final then
        FinalFrame(sequenceNumber, iv, plaintext, authTag)
      else
        RegularFrame(sequenceNumber, iv, plaintext, authTag);

    ghost var encryptedFrame := if final then
        FinalFrame(sequenceNumber, iv, ciphertext, authTag)
      else
        RegularFrame(sequenceNumber, iv, ciphertext, authTag);

    // Feed dafny facts about the content of the stream
    // Show dafny that the serialized frame is frameSerialization
    assert frameSerialization == FrameToSequence(encryptedFrame);

    // Prove read content of stream is frameSerialization
    assert {:focus} true;
    assert !final ==> frameSerialization[..4] == rd.reader.data[old(rd.reader.pos)..][..4];
    assert !final ==> frameSerialization[4..][..suite.encrypt.ivLength as int] == rd.reader.data[old(rd.reader.pos)..][4..][..suite.encrypt.ivLength as int];
    assert !final ==> frameSerialization[4 + suite.encrypt.ivLength as int..][..frameLength] == rd.reader.data[old(rd.reader.pos)..][4 + suite.encrypt.ivLength as int..][..frameLength];
    assert !final ==> frameSerialization[4 + frameLength + suite.encrypt.ivLength as int..] == rd.reader.data[old(rd.reader.pos)..][4 + frameLength + suite.encrypt.ivLength as int..][..suite.encrypt.tagLength as int];

    // Prove equivalence frameSerialization and content read on the stream
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == frameSerialization;

    assert old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|;

    return Success(FrameWithGhostSeq(frame,ciphertext));
  }

  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    aad := messageID + contentAAD.value + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(
    ciphertext: seq<uint8>,
    authTag: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    iv: seq<uint8>,
    key: seq<uint8>,
    aad: seq<uint8>
  )
    returns (res: Result<seq<uint8>, string>)
    requires 
      && |iv| == suite.encrypt.ivLength as int
      && |key| == suite.encrypt.keyLength as int
      && |authTag| == suite.encrypt.tagLength as int
    ensures res.Success? ==> AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, res.value)
    ensures res.Success? ==> |ciphertext| == |res.value|
    ensures res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value)
  {
    var encAlg := suite.encrypt;
    res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
    assert res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value);
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

  method DecryptNonFramedMessageBody(
    rd: Streams.ByteReader,
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    key: seq<uint8>,
    messageID: Msg.MessageID
  )
    returns (res: Result<seq<uint8>, string>)
    requires rd.Valid()
    requires |key| == suite.encrypt.keyLength as int
    modifies rd.reader`pos
    ensures rd.Valid()
  {
    var iv :- rd.ReadBytes(suite.encrypt.ivLength as int);
    var contentLength :- rd.ReadUInt64();
    var ciphertext :- rd.ReadBytes(contentLength as nat);
    var authTag :- rd.ReadBytes(suite.encrypt.tagLength as int);

    var aad := BodyAAD(messageID, AADSingleBlock, NONFRAMED_SEQUENCE_NUMBER, contentLength);

    var plaintext :- Decrypt(ciphertext, authTag, suite, iv, key, aad);
    return Success(plaintext);
  }
}
