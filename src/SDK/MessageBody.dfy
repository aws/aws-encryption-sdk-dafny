include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "MessageHeader.dfy"
include "AlgorithmSuite.dfy"
include "../Crypto/AESEncryption.dfy"
include "Materials.dfy"
include "../Util/Streams.dfy"
include "../Crypto/EncryptionSuites.dfy"
include "../Util/UTF8.dfy"

module MessageBody {
  export
    provides EncryptMessageBody, DecryptFramedMessageBody, DecryptNonFramedMessageBody,
      StandardLibrary, UInt, Msg, AlgorithmSuite, Materials, Streams, FramesToSequence, 
      FrameToSequence, ValidFrames, FramesEncryptPlaintext
    reveals Frame, Frame.Valid
    
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Msg = MessageHeader
  import AESEncryption
  import Materials
  import Streams
  import EncryptionSuites
  import UTF8

  datatype BodyAADContent = RegularFrame | FinalFrame | SingleBlock

  /**
    The behviour of the methods in this file are specified in https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/data-format/message-body.md
    The Frame datatype has been introduced in the validation of this file. This datatype is only used for the validation. 
    The methods in this file serialize and deserialize some plaintext to frames. Frame are encoded in a sequence of bytes.
    All frames beside the last frame are RegularFrames, the last frame is a FinalFrame. All frames have a unique iv and an incrementing sequence numbers. Sequence numbers
    start from START_SEQUENCE_NUMBER and go up to ENDFRAME_SEQUENCE_NUMBER. Note that the final frame can occur before ENDFRAME_SEQUENCE_NUMBER is reached.

    Regular frames always contain the same amount of data and contain 4 fields: RegularFrameConstructor(seqNumb, iv, encContent, authTag)
    We know the length of serialized regular frames in advance. Every regular frame has size 4 + IV_Length + frameLength + authTag_Length.
    Here framelength is the length of the encrypted content which is equal to the plaintext serialized in this frame.

    Final frames have more data fields and contain a variable amount of encrypted content. When a final frame is serialized it has 6 fields:
      FinalFrame(endFrameSeqNumb, seqNumb, iv, encryptedContentLength, encryptedContent, authtag)
        Here endFrameSeqNumb is an identifier which tells the parser it is parsing a final frame. This variable is always equal to ENDFRAME_SEQUENCE_NUMBER
        seqNumb is the actual sequence number of the final frame which does not have to be ENDFRAME_SEQUENCE_NUMBER.
        encruptedContentLength is the length of the encrypted content which is an uint32. The encrypted content is at most equal to the framelength.
    We know that the serialized final frame length is between 4 + 4 + IV_Length + 4 + 0 + authTag_Length and 4 + 4 + IV_Length + 4 + frameLength + authTag_Length
  */

  predicate ValidFrames(frames: seq<Frame>) {
    0 < |frames| < UINT32_LIMIT &&
    forall i | 0 <= i < |frames| ::
      var frame := frames[i];
      frame.Valid() &&
      (if i == |frames| - 1 then frame.FinalFrameConstructor? else frame.RegularFrameConstructor?) &&
      frame.seqNumb as int == i + START_SEQUENCE_NUMBER as int &&
      (forall j | i < j < |frames| :: frame.iv != frames[j].iv)
  }

  datatype Frame = RegularFrameConstructor(seqNumb: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) |
                   FinalFrameConstructor(seqNumb: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>)
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
    case RegularFrame => BODY_AAD_CONTENT_REGULAR_FRAME
    case FinalFrame => BODY_AAD_CONTENT_FINAL_FRAME
    case SingleBlock => BODY_AAD_CONTENT_SINGLE_BLOCK
  }

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := 1

  function method IVSeq(algorithmSuiteID: AlgorithmSuite.ID, sequenceNumber: uint32): seq<uint8> {
    seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber)
  }

  lemma IVSeqDistinct(algorithmSuiteID: AlgorithmSuite.ID, m: uint32, n: uint32)
    requires m != n
    ensures IVSeq(algorithmSuiteID, m) != IVSeq(algorithmSuiteID, n)
  {
    var paddingLength := algorithmSuiteID.IVLength() - 4;
    assert IVSeq(algorithmSuiteID, m)[paddingLength..] == UInt32ToSeq(m);
    assert IVSeq(algorithmSuiteID, n)[paddingLength..] == UInt32ToSeq(n);
    UInt32SeqSerializeDeserialize(m);
    UInt32SeqSerializeDeserialize(n);
  }

  // Converts sequence of Frames to a sequence encoding all frames
  function FramesToSequence(frames : seq<Frame>): seq<uint8>
    requires |frames| < UINT32_LIMIT
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
      case RegularFrameConstructor(_, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) =>
        4 + |iv| + |encContent| + |authTag| == |res|
      case FinalFrameConstructor(seqNumb: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) =>
        4 + 4 + |iv| + 4 + |encContent| + |authTag| == |res|
  {
    match frame 
      case RegularFrameConstructor(seqNumb, iv, encContent, authTag) =>
        var seqNumSeq := UInt32ToSeq(seqNumb);
        seqNumSeq + iv + encContent + authTag
      case FinalFrameConstructor(seqNumb, iv, encContent, authTag) =>
        var seqNumbEndSeq := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
        var seqNumbSeq := UInt32ToSeq(seqNumb);
        var encContentLengthSeq := UInt32ToSeq(|encContent| as uint32);
        seqNumbEndSeq + seqNumbSeq + iv + encContentLengthSeq + encContent + authTag
  }
 
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
           FramesEncryptPlaintextSegments(frames[..|frames|-1], plaintextSeg[..|frames|-1]) 
        && AESEncryption.CiphertextGeneratedWithPlaintext(frames[|frames|-1].encContent, plaintextSeg[|frames|-1])
  }

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
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg|-1]) + plaintextSeg[|plaintextSeg|-1]
  }

  lemma ExtendSumPlaintextSegments(plaintextSeg: seq<seq<uint8>>, plaintextFrame: seq<uint8>)
    ensures SumPlaintextSegments(plaintextSeg + [plaintextFrame]) == SumPlaintextSegments(plaintextSeg) + plaintextFrame
  {
  }

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID)
      returns (result: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    ensures match result
      case Failure(e) => true
      case Success(resultSuccess) => exists frames: seq<Frame> | ValidFrames(frames) ::
        && FramesToSequence(frames) == resultSuccess
        && FramesEncryptPlaintext(frames, plaintext)
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
      invariant forall i | 0 <= i < |frames| ::
        var frame := frames[i];
        frame.Valid() &&
        frame.RegularFrameConstructor? &&
        frame.seqNumb as int == i + START_SEQUENCE_NUMBER as int
      invariant forall i | 0 <= i < |frames| :: frames[i].iv == IVSeq(algorithmSuiteID, frames[i].seqNumb)
      invariant FramesToSequence(frames) == body
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg)
      invariant SumPlaintextSegments(plaintextSeg) == plaintext[..n]
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure("too many frames");
      }
      var plaintextFrame := plaintext[n..n + frameLength];
      var regularFrame, frame := EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      if regularFrame.IsFailure() {
        return regularFrame.PropagateFailure();
      }
      assert frame.iv == IVSeq(algorithmSuiteID, sequenceNumber);
      ExtendFramesToSequence(frames, frame);
      ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, frame, plaintextFrame);
      ExtendSumPlaintextSegments(plaintextSeg, plaintextFrame);
      frames := frames + [frame];
      body := body + regularFrame.Extract();
      plaintextSeg := plaintextSeg + [plaintextFrame];
      
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
      assert SumPlaintextSegments(plaintextSeg) == plaintext[..n];
    }

    var finalFrameResult, finalFrame := EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    if finalFrameResult.IsFailure() {
      return finalFrameResult.PropagateFailure();
    }
    var finalFrameSequence := finalFrameResult.Extract();
    assert finalFrame.iv == IVSeq(algorithmSuiteID, sequenceNumber);
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
        assert frames[i].seqNumb as int == i + START_SEQUENCE_NUMBER as int;
        assert frames[j].seqNumb as int == j + START_SEQUENCE_NUMBER as int;
        assert frames[i].iv == IVSeq(algorithmSuiteID, frames[i].seqNumb);
        assert frames[j].iv == IVSeq(algorithmSuiteID, frames[j].seqNumb);
        IVSeqDistinct(algorithmSuiteID, frames[i].seqNumb, frames[j].seqNumb);
      }
    }

    result := Success(body);
  }

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, ghost frameLength: int,
                             messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>, ghost regFrame: Frame)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res 
      case Failure(e) => true
      case Success(resultSuccess) => 
           4 + algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength() + frameLength == |resultSuccess|
        && var iv := IVSeq(algorithmSuiteID, sequenceNumber);
           var encContent := resultSuccess[4 + algorithmSuiteID.IVLength()..4 + algorithmSuiteID.IVLength() + frameLength];
           var authTag := resultSuccess[4 + algorithmSuiteID.IVLength() + frameLength..];
           var frame := RegularFrameConstructor(sequenceNumber, iv, encContent, authTag);
           frame == regFrame
        && FrameToSequence(regFrame) == resultSuccess
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := IVSeq(algorithmSuiteID, sequenceNumber);
    var aad := BodyAAD(messageID, RegularFrame, sequenceNumber, |plaintext| as uint64);
    
    var encryptionOutputResult := AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    ghost var frame := RegularFrameConstructor(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);

    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

    return Success(unauthenticatedFrame), frame;
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, 
                           messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>, ghost finalFrame: Frame)
    requires |key| == algorithmSuiteID.KeyLength()
    requires START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires 0 <= |plaintext| < UINT32_LIMIT
    requires |plaintext| <= frameLength
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res 
      case Failure(e) => true
      case Success(resultSuccess) => 
           4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() <= |resultSuccess| 
            <= 4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() + frameLength
        && var contentLength : uint32 := SeqToUInt32(resultSuccess[4+4+algorithmSuiteID.IVLength()..4+4+algorithmSuiteID.IVLength()+4]);
           |resultSuccess| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + contentLength as int + algorithmSuiteID.TagLength() 
        && resultSuccess[..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER)
        && |plaintext| == SeqToUInt32(resultSuccess[4 + 4 + algorithmSuiteID.IVLength()..4 + 4 + algorithmSuiteID.IVLength() + 4]) as int &&
           var iv := IVSeq(algorithmSuiteID, sequenceNumber);
           var encContent := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4..][..|plaintext|];
           var authTag := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext|..];
           var frame := FinalFrameConstructor(sequenceNumber, iv, encContent, authTag);
           FrameToSequence(frame) == resultSuccess
        && finalFrame == frame
        && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;

    var iv := IVSeq(algorithmSuiteID, sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);

    var aad := BodyAAD(messageID, FinalFrame, sequenceNumber, |plaintext| as uint64);

    var encryptionOutputResult := AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    assert |plaintext| == |encryptionOutput.cipherText|;

    ghost var frame := FinalFrameConstructor(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    finalFrame := frame;
    assert FrameToSequence(frame) == unauthenticatedFrame;

    assert |plaintext| == SeqToUInt32(unauthenticatedFrame[4 + 4 + algorithmSuiteID.IVLength()..4 + 4 + algorithmSuiteID.IVLength() + 4]) as int;
    assert |unauthenticatedFrame| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext| + algorithmSuiteID.TagLength();

    assert unauthenticatedFrame[4 + 4 + algorithmSuiteID.IVLength() + 4..][..|plaintext|] == encryptionOutput.cipherText;

    return Success(unauthenticatedFrame), finalFrame;
  }

  method DecryptFramedMessageBody(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID) 
      returns (res: Result<seq<uint8>>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res
      case Failure(_) => true
      case Success(plaintext) => 
        old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| 
        && exists frames: seq<Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid()) 
            && FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos] :: 
              FramesEncryptPlaintext(frames, plaintext)
  {
    var plaintext := [];
    var n: uint32 := 1;
    ghost var frames: seq<Frame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := []; 

    while true
      decreases ENDFRAME_SEQUENCE_NUMBER - n
      invariant rd.Valid()
      invariant n as int - 1 == |frames|
      invariant n <= ENDFRAME_SEQUENCE_NUMBER
      invariant forall frame | frame in frames :: frame.Valid()
      invariant old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
      invariant FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      invariant rd.Valid()
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg)
      invariant SumPlaintextSegments(plaintextSeg) == plaintext
    {
      var frameWithGhostSeq :- DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, n);
      assert |frameWithGhostSeq.ciphertext| < UINT32_LIMIT;
      var decryptedFrame := frameWithGhostSeq.frame;
      ghost var ciphertext := frameWithGhostSeq.ciphertext;
      assert |ciphertext| < UINT32_LIMIT;
      ghost var encryptedFrame := if decryptedFrame.FinalFrameConstructor? then
        FinalFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
      else
        RegularFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, ciphertext, decryptedFrame.authTag);
      assert encryptedFrame.Valid();
      frames := frames + [encryptedFrame];

      var (framePlaintext, final) := (decryptedFrame.encContent, decryptedFrame.FinalFrameConstructor?);
      
      plaintext := plaintext + framePlaintext;
      plaintextSeg := plaintextSeg + [framePlaintext];
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

  datatype FrameWithGhostSeq = FrameWithGhostSeq(frame: Frame, ghost ciphertext: seq<uint8>)

  method DecryptFrame(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID,
                      expectedSequenceNumber: uint32)
      returns (res: Result<FrameWithGhostSeq>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res // If the expeced sequence number is the end frame sequence number then the frame is the final frame. However the final frame can arrive earlier
      case Success(frameWithGhostSeq) =>
        expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> frameWithGhostSeq.frame.FinalFrameConstructor? 
      case Failure(_) => true
    ensures res.Success? ==> |res.value.ciphertext| < UINT32_LIMIT
    ensures match res
      case Success(frameWithGhostSeq) => (
           var decryptedFrame := frameWithGhostSeq.frame;
           var ciphertext := frameWithGhostSeq.ciphertext;
           var final := decryptedFrame.FinalFrameConstructor?;
           decryptedFrame.Valid()
        && old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|
        && AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, decryptedFrame.encContent)      
        && var encryptedFrame := (if decryptedFrame.FinalFrameConstructor? then
             FinalFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)
           else
             RegularFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, ciphertext, decryptedFrame.authTag)); 
           rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == FrameToSequence(encryptedFrame)   
        && AESEncryption.CiphertextGeneratedWithPlaintext(encryptedFrame.encContent, decryptedFrame.encContent))
      case Failure(_) => true
  {    
    var final := false;
    var sequenceNumber :- rd.ReadUInt32(); 
    ghost var sequence := UInt32ToSeq(sequenceNumber);
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;
    
    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
      sequence := sequence + UInt32ToSeq(sequenceNumber);
      assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;
    }
    
    if sequenceNumber != expectedSequenceNumber {
      return Failure("unexpected frame sequence number");
    }

    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    sequence := sequence + iv;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;

    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
      if len > frameLength as uint32 {
        return Failure("Final frame too long");
      }
      sequence := sequence + UInt32ToSeq(len);
    }

    var aad := BodyAAD(messageID, if final then FinalFrame else RegularFrame, sequenceNumber, len as uint64);

    var ciphertext :- rd.ReadBytes(len as nat);
    sequence := sequence + ciphertext;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;
    
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    sequence := sequence + authTag;
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;

    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    assert AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, plaintext);
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;

    var frame := if final then
        FinalFrameConstructor(sequenceNumber, iv, plaintext, authTag)
      else 
        RegularFrameConstructor(sequenceNumber, iv, plaintext, authTag);

    ghost var encryptedFrame := if final then
        FinalFrameConstructor(sequenceNumber, iv, ciphertext, authTag)
      else 
        RegularFrameConstructor(sequenceNumber, iv, ciphertext, authTag);    

    // Feed dafny facts about the content of the stream
    // Show dafny that the serialized frame is sequence
    assert sequence == FrameToSequence(encryptedFrame);

    // Prove read content of stream is sequence 
    assert !final ==> sequence[..4] == rd.reader.data[old(rd.reader.pos)..][..4];
    assert !final ==> sequence[4..][..algorithmSuiteID.IVLength()] == rd.reader.data[old(rd.reader.pos)..][4..][..algorithmSuiteID.IVLength()];
    assert !final ==> sequence[4 + algorithmSuiteID.IVLength()..][..frameLength] == rd.reader.data[old(rd.reader.pos)..][4 + algorithmSuiteID.IVLength()..][..frameLength];
    assert !final ==> sequence[4 + frameLength + algorithmSuiteID.IVLength()..] == rd.reader.data[old(rd.reader.pos)..][4 + frameLength + algorithmSuiteID.IVLength()..][..algorithmSuiteID.TagLength()];

    // Prove equivalence sequence and content read on the stream
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;

    assert old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|;     

    return Success(FrameWithGhostSeq(frame,ciphertext));
  }

  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    aad := messageID + contentAAD.value + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(ciphertext: seq<uint8>, authTag: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, aad: seq<uint8>) returns (res: Result<seq<uint8>>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    requires |authTag| == algorithmSuiteID.TagLength()
    ensures res.Success? ==> AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, res.value)
    ensures res.Success? ==> |ciphertext| == |res.value|
  {
    var encAlg := algorithmSuiteID.EncryptionSuite();
    res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
  }

  method DecryptNonFramedMessageBody(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, messageID: Msg.MessageID) returns (res: Result<seq<uint8>>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    modifies rd.reader`pos
    ensures rd.Valid()
  {
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    var contentLength :- rd.ReadUInt64();
    var ciphertext :- rd.ReadBytes(contentLength as nat);
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());

    var aad := BodyAAD(messageID, SingleBlock, NONFRAMED_SEQUENCE_NUMBER, contentLength);

    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    return Success(plaintext);
  }
}