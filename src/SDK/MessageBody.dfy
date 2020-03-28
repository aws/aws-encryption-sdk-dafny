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
    //provides EncryptMessageBody
    provides DecryptFramedMessageBody, DecryptNonFramedMessageBody
    provides StandardLibrary, UInt, Msg, AlgorithmSuite, Materials, Streams
    provides FramesToSequence, FrameToSubsequence, ValidFrames, EncryptedFramesToPlaintext
    reveals Frame
    
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

  predicate ValidFrames(frames: seq<Frame>) {
         0 < |frames| < UINT32_LIMIT
      && forall frame | frame in frames :: frame.Valid()   
      && forall frame | frame in frames :: |frame.encContent| < UINT32_LIMIT 
      && frames[|frames| - 1].FinalFrameConstructor?
      && forall frame | frame in frames[..|frames| - 1] :: frame.RegularFrameConstructor?
      && forall i | 0 <= i < |frames| :: frames[i].seqNumb as int == i + START_SEQUENCE_NUMBER as int
      && forall i, j | 0 <= i < j < |frames| :: frames[i].iv != frames[j].iv  
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

  //Parses a sequence encoding a regular frame to a regular frame datastructure
  function SubsequenceToRegularFrame(serializedFrame: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, frameLength: int): (frame: Frame)
    requires 0 < frameLength < UINT32_LIMIT
    requires 4 + algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength() + frameLength == |serializedFrame|;
    ensures frame.RegularFrameConstructor?
    ensures frame.Valid()
    ensures FrameToSubsequence(frame) == serializedFrame
  {
    var sqn := SeqToUInt32(serializedFrame[0..4]);
    var ivEnd := algorithmSuiteID.IVLength() +  4;
    var encryptEnd := ivEnd + frameLength;
    RegularFrameConstructor(sqn,serializedFrame[4..ivEnd],serializedFrame[ivEnd..encryptEnd],serializedFrame[encryptEnd..])
  }

  //Parses a sequence encoding a final frame to a final frame datastructure
  function SubsequenceToFinalFrame(serializedFrame: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, frameLength: int): (frame: Frame)
    requires 4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() <= |serializedFrame|;
    requires var contentLength : uint32 := SeqToUInt32(serializedFrame[4+4+algorithmSuiteID.IVLength()..4+4+algorithmSuiteID.IVLength()+4]);
             |serializedFrame| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + contentLength as int + algorithmSuiteID.TagLength() &&
             0 <= contentLength as int <= frameLength
    requires serializedFrame[..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    ensures frame.FinalFrameConstructor?
    ensures frame.Valid()
    ensures FrameToSubsequence(frame) == serializedFrame
  {
    var sqn := SeqToUInt32(serializedFrame[4..8]);
    var ivEnd := algorithmSuiteID.IVLength() +  8;
    var frameLength := SeqToUInt32(serializedFrame[ivEnd..ivEnd+4]);
    var encryptEnd := 4 + 4 + algorithmSuiteID.IVLength() + 4 + frameLength as int;
    assert frameLength as int == |serializedFrame[ivEnd+4..encryptEnd]|;
    FinalFrameConstructor(sqn, serializedFrame[8..ivEnd], serializedFrame[ivEnd+4..encryptEnd], serializedFrame[encryptEnd..])
  }
    

  //Converts sequence of Frames to a sequence encoding all frames
  function FramesToSequence(frames : seq<Frame>): seq<uint8>
    requires |frames| < UINT32_LIMIT
    requires forall frame | frame in frames :: frame.Valid()
  {
    if frames == [] then
      []
    else
      FramesToSequence(frames[..|frames| - 1]) + FrameToSubsequence(frames[|frames| - 1])
  }

  //Converts Frame to a sequence encoding a frame
  function FrameToSubsequence(frame: Frame): (res: seq<uint8>)
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

  //Adds assumption that the size of the encrypted content isn't above the allowed limit. 
  function EncryptMock (input: seq<uint8>):  (output: seq<uint8>)
    ensures |input| == |output|
    ensures DecryptMock(EncryptMock(input)) == input;

  function DecryptMock (input: seq<uint8>): (output: seq<uint8>)
    ensures |input| == |output|

  function EncryptedFramesToPlaintext(frames: seq<Frame>): (plaintext: seq<uint8>)
  {
    if frames == [] then
      []
    else
      EncryptedFramesToPlaintext(frames[..|frames|-1]) + DecryptMock(frames[|frames|-1].encContent)
  }

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID)
      returns (result: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    requires |plaintext| < UINT32_LIMIT*frameLength
   ensures match result //create Datatype/predicate
      case Failure(e) => true
      case Success(resultSuccess) => exists frames: seq<Frame> | ValidFrames(frames)::
        && FramesToSequence(frames) == resultSuccess
  { 
    var body := [];
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    ghost var frames : seq<Frame> := [];
    
    while n + frameLength < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant forall frame | frame in frames :: frame.Valid()
      invariant |frames| == (sequenceNumber - START_SEQUENCE_NUMBER) as int
      invariant FramesToSequence(frames) == body
      invariant forall frame | frame in frames :: frame.RegularFrameConstructor?
      invariant forall i | 0 <= i < |frames| :: frames[i].seqNumb as int == i + START_SEQUENCE_NUMBER as int
      invariant forall frame | frame in frames :: frame.iv == seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(frame.seqNumb)
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure("too many frames");
      }
      var plaintextFrame := plaintext[n..n + frameLength];
      var regularFrame :- EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
    
      ghost var frame := SubsequenceToRegularFrame(regularFrame, algorithmSuiteID, frameLength);
      frames := frames + [frame];

      body := body + regularFrame;
      assert FramesToSequence(frames) == body;
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
    }
    var FinalFrame :- EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    
    body := body + FinalFrame;
    ghost var frame := SubsequenceToFinalFrame(FinalFrame, algorithmSuiteID, frameLength);
    frames := frames + [frame];
    
    assert frame.iv  == seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(frame.seqNumb);
    assert forall frame | frame in frames :: frame.iv == seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(frame.seqNumb);
    assert forall i | 0 <= i < |frames| :: frames[i].seqNumb as int == i + START_SEQUENCE_NUMBER as int;
    IVDependsOnSequenceNumber(frames, algorithmSuiteID);
    assert forall i, j | 0 <= i < j < |frames| :: frames[i].iv != frames[j].iv;
    assert ValidFrames(frames);
    
    return Success(body);
  }

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, ghost frameLength: int,
                             messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res 
      case Failure(e) => true
      case Success(resultSuccess) => 
        4 + algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength() + frameLength == |resultSuccess| &&
        var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
        var encContent := resultSuccess[4 + algorithmSuiteID.IVLength()..4 + algorithmSuiteID.IVLength() + frameLength];
        var authTag := resultSuccess[4 + algorithmSuiteID.IVLength() + frameLength..];
        var frame := RegularFrameConstructor(sequenceNumber, iv, encContent, authTag);
        FrameToSubsequence(frame) == resultSuccess;
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
    var aad := BodyAAD(messageID, RegularFrame, sequenceNumber, |plaintext| as uint64);
    var encryptionOutput :- AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    isEncrypted(plaintext, encryptionOutput.cipherText);
    
    ghost var frame := RegularFrameConstructor(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);

    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    
    return Success(unauthenticatedFrame);
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int,
                           messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
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
           var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
           var encContent := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4..][..|plaintext|]; //Is there a better way to do this
           var authTag := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext|..];
           var frame := FinalFrameConstructor(sequenceNumber, iv, encContent, authTag);
           FrameToSubsequence(frame) == resultSuccess
        && SubsequenceToFinalFrame(resultSuccess, algorithmSuiteID, frameLength) == frame
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;
    
    var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);
    
    var aad := BodyAAD(messageID, FinalFrame, sequenceNumber, |plaintext| as uint64);
    
    var encryptionOutput :- AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    isEncrypted(plaintext, encryptionOutput.cipherText);
    assert |plaintext| == |encryptionOutput.cipherText|;

    ghost var frame := FinalFrameConstructor(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    assert FrameToSubsequence(frame) == unauthenticatedFrame;
    assert SubsequenceToFinalFrame(unauthenticatedFrame, algorithmSuiteID, frameLength) == frame;

    return Success(unauthenticatedFrame);
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
        old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| &&
        exists frames: seq<Frame> | 
           |frames| < UINT32_LIMIT 
        && (forall frame | frame in frames :: frame.Valid()) 
        && FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos] :: 
            EncryptedFramesToPlaintext(frames) == plaintext
  {
    var plaintext := [];
    var n: uint32 := 1;
    ghost var frames: seq<Frame> := []; 
    while true
      decreases ENDFRAME_SEQUENCE_NUMBER - n
      invariant rd.Valid()
      invariant n as int - 1 == |frames|
      invariant n <= ENDFRAME_SEQUENCE_NUMBER
      invariant forall frame | frame in frames :: frame.Valid()
      invariant old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
      invariant FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      invariant EncryptedFramesToPlaintext(frames) == plaintext
    {
      var decryptedFrame :- DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, n);
      ghost var encryptedFrame := if decryptedFrame.FinalFrameConstructor? then
        FinalFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, EncryptMock(decryptedFrame.encContent),decryptedFrame.authTag)
      else
        RegularFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, EncryptMock(decryptedFrame.encContent),decryptedFrame.authTag);
      frames := frames + [encryptedFrame];
      var (framePlaintext, final) := (decryptedFrame.encContent, decryptedFrame.FinalFrameConstructor?);

      assert framePlaintext == DecryptMock(encryptedFrame.encContent);

      plaintext := plaintext + framePlaintext;
      if final {
        break;
      }
      n := n + 1;
    }
    assert |frames| < UINT32_LIMIT ;
    assert (forall frame | frame in frames :: frame.Valid()) ;
    assert FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]; 
    assert EncryptedFramesToPlaintext(frames) == plaintext;
    return Success(plaintext);
  }

  method DecryptFrame(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID,
                      expectedSequenceNumber: uint32)
      returns (res: Result<Frame>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res
      case Success(frame) =>
        expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> frame.FinalFrameConstructor?  // but "final" may come up before this
      case Failure(_) => true
    ensures match res
      case Success(decryptedFrame) =>
           decryptedFrame.Valid() 
        && var encryptedFrame := if decryptedFrame.FinalFrameConstructor? then
             FinalFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, EncryptMock(decryptedFrame.encContent),decryptedFrame.authTag)
           else
             RegularFrameConstructor(decryptedFrame.seqNumb, decryptedFrame.iv, EncryptMock(decryptedFrame.encContent),decryptedFrame.authTag);
        && old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|   
        && rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == FrameToSubsequence(encryptedFrame)   
        && EncryptMock(decryptedFrame.encContent) == encryptedFrame.encContent
        && decryptedFrame.encContent == DecryptMock(encryptedFrame.encContent)
      case Failure(_) => true
  {    
    var final := false;
    var sequenceNumber :- rd.ReadUInt32(); 
    ghost var sequence := UInt32ToSeq(sequenceNumber);
    
    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
      sequence := sequence + UInt32ToSeq(sequenceNumber);
    }
    
    if sequenceNumber != expectedSequenceNumber {
      return Failure("unexpected frame sequence number");
    }
  
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());

    sequence := sequence + iv;
    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
      sequence := sequence + UInt32ToSeq(len);
    }
    
    var aad := BodyAAD(messageID, if final then FinalFrame else RegularFrame, sequenceNumber, len as uint64);

    var ciphertext :- rd.ReadBytes(len as nat);
    sequence := sequence + ciphertext;
    
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    sequence := sequence + authTag;

    
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    isEncrypted(plaintext, ciphertext);
    
    var frame := if final then
        FinalFrameConstructor(sequenceNumber, iv, plaintext, authTag)
      else 
        RegularFrameConstructor(sequenceNumber, iv, plaintext, authTag);

    ghost var encryptedFrame := if final then
        FinalFrameConstructor(sequenceNumber, iv, ciphertext, authTag)
      else 
        RegularFrameConstructor(sequenceNumber, iv, ciphertext, authTag);    
    
    //Feed dafny facts about the content of the stream
    //Show dafny that the serialized frame is sequence
    assert sequence == FrameToSubsequence(encryptedFrame);
    
    //Give dafny information about the content of the stream
    assert !final ==> UInt32ToSeq(sequenceNumber) == rd.reader.data[old(rd.reader.pos)..][..4];
    assert !final ==> iv == rd.reader.data[old(rd.reader.pos)..][4..][..algorithmSuiteID.IVLength()];
    assert !final ==> ciphertext == rd.reader.data[old(rd.reader.pos)..][4+algorithmSuiteID.IVLength()..][..frameLength];
    assert !final ==> authTag == rd.reader.data[old(rd.reader.pos)..][4+frameLength+algorithmSuiteID.IVLength()..][..algorithmSuiteID.TagLength()];
    assert final ==> UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER) == rd.reader.data[old(rd.reader.pos)..][..4];
    assert final ==> UInt32ToSeq(sequenceNumber) == rd.reader.data[old(rd.reader.pos)..][4..][..4];
    assert final ==> iv == rd.reader.data[old(rd.reader.pos)..][8..][..algorithmSuiteID.IVLength()];
    assert final ==> UInt32ToSeq(len) == rd.reader.data[old(rd.reader.pos)..][8+algorithmSuiteID.IVLength()..][..4];
    assert final ==> ciphertext == rd.reader.data[old(rd.reader.pos)..][12+algorithmSuiteID.IVLength()..][..len as int];
    assert final ==> authTag == rd.reader.data[old(rd.reader.pos)..][12+algorithmSuiteID.IVLength()+len as int..][..algorithmSuiteID.TagLength()];

    //Prove equivalence read stream and sequence normal case 
    assert !final ==> sequence[..4] == rd.reader.data[old(rd.reader.pos)..][..4];
    assert !final ==> sequence[4..][..algorithmSuiteID.IVLength()] == rd.reader.data[old(rd.reader.pos)..][4..][..algorithmSuiteID.IVLength()];
    assert !final ==> sequence[4+algorithmSuiteID.IVLength()..][..frameLength] == rd.reader.data[old(rd.reader.pos)..][4+algorithmSuiteID.IVLength()..][..frameLength];
    assert !final ==> sequence[4+frameLength+algorithmSuiteID.IVLength()..] == rd.reader.data[old(rd.reader.pos)..][4+frameLength+algorithmSuiteID.IVLength()..][..algorithmSuiteID.TagLength()];

    //Prove equivalence sequence and content read on the stream
    assert rd.reader.data[old(rd.reader.pos)..rd.reader.pos] == sequence;
    
    return Success(frame);
  }

  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    aad := messageID + contentAAD.value + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(ciphertext: seq<uint8>, authTag: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, aad: seq<uint8>) returns (res: Result<seq<uint8>>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    requires |authTag| == algorithmSuiteID.TagLength()
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

  lemma IVDependsOnSequenceNumber(frames: seq<Frame>, algorithmSuiteID: AlgorithmSuite.ID)
  requires forall frame | frame in frames :: frame.iv == seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(frame.seqNumb)
  requires forall i | 0 <= i < |frames| :: frames[i].seqNumb as int == i + 1
  ensures forall frame1, frame2 | frame1 in frames && frame2 in frames && frame1 != frame2 :: frame1.iv != frame2.iv
  {
    if(|frames| < 2){

    }else{
      var front := seq(algorithmSuiteID.IVLength() - 4, _ => 0);
      calc{
          forall i,j | 0 <= i < j < |frames| :: frames[i].seqNumb != frames[j].seqNumb;
        <==>
          forall i,j | 0 <= i < j < |frames| :: UInt32ToSeq(frames[i].seqNumb) != UInt32ToSeq(frames[j].seqNumb);
        <==> { forall back1: seq<uint8>, back2: seq<uint8>, front: seq<uint8> | back1 != back2
              {
                PrependPreservesInequality(back1, back2, front);
              }
            }
            forall i, j | 0 <= i < j < |frames| :: front + UInt32ToSeq(frames[i].seqNumb) != front + UInt32ToSeq(frames[j].seqNumb);
        <==> {assert forall i | 0 <= i < |frames| :: frames[i].iv == front + UInt32ToSeq(frames[i].seqNumb);}
          forall i, j | 0 <= i < j < |frames| :: frames[i].iv != frames[j].iv;
      }
    }
  }

  lemma PrependPreservesInequality(back1: seq<uint8>, back2: seq<uint8>, front: seq<uint8>)
    requires back1 != back2
    ensures front + back1 != front + back2
  {
    if(front + back1 == front + back2){
      calc{
        front + back1 == front + back2;
      <==> 
        (front + back1)[|front|..] == (front + back2)[|front|..];
      <==>
        back1 == back2;
      }
    }else{
        
    }
  }

  lemma {:axiom} isEncrypted(plaintext: seq<uint8>, encContent: seq<uint8>)
    ensures EncryptMock(plaintext) == encContent
    ensures DecryptMock(encContent) == plaintext
}
