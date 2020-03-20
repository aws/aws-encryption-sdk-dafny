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
    provides EncryptMessageBody
    provides DecryptFramedMessageBody, DecryptNonFramedMessageBody
    provides StandardLibrary, UInt, Msg, AlgorithmSuite, Materials, Streams
    provides FramesToSequence, FrameToSubsequence
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
  datatype Frame = RegFrameCons(seqNumb: uint32, iv: seq<uint8>, encCont: seq<uint8>, authTag: seq<uint8>) |
                   FinalFrameCons(seqNumbEnd: uint32, seqNumb: uint32, iv: seq<uint8>, encContLength: uint32, encCont: seq<uint8>, authTag: seq<uint8>)

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
  function SubsequenceToRegFrame(xs: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID,frameLength: int): (f: Frame)
    requires |xs| == 4 + algorithmSuiteID.IVLength() + frameLength + algorithmSuiteID.TagLength();
    requires 0 < frameLength < UINT32_LIMIT
    requires 0 <= algorithmSuiteID.IVLength()
    ensures f.RegFrameCons?
    ensures |f.iv| == algorithmSuiteID.IVLength()
    ensures |f.encCont| == frameLength;
    ensures |f.authTag| == algorithmSuiteID.TagLength()
    ensures FrameToSubsequence(f) == xs
  {
    var sqn := SeqToUInt32(xs[0..4]);
    var ivEnd := algorithmSuiteID.IVLength() +  4;
    var encryptEnd := ivEnd + frameLength;
    RegFrameCons(sqn,xs[4..ivEnd],xs[ivEnd..ivEnd+encryptEnd],xs[encryptEnd..])
  }

  //Parses a sequence encoding a final frame to a final frame datastructure
  function SubsequenceToFinalFrame(xs: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, frameLength: int): (f: Frame)
    requires 4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() <= |xs| <= 4 + 4 + algorithmSuiteID.IVLength() + 4 + frameLength + algorithmSuiteID.TagLength();
    requires 0 <= algorithmSuiteID.IVLength();
    requires 0 < frameLength < UINT32_LIMIT
    requires var fl : uint32 := SeqToUInt32(xs[4+4+algorithmSuiteID.IVLength()..4+4+algorithmSuiteID.IVLength()+4]);
             0 <= fl <= frameLength as uint32 &&
             |xs| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + fl as int + algorithmSuiteID.TagLength() 
    requires 0 < algorithmSuiteID.TagLength()
    ensures f.FinalFrameCons?
    ensures |f.iv| == algorithmSuiteID.IVLength()
    ensures |f.iv| == algorithmSuiteID.IVLength()
    ensures |f.encCont| == frameLength;
    ensures |f.authTag| == algorithmSuiteID.TagLength()
    ensures FrameToSubsequence(f) == xs
  {
    var sqnE := SeqToUInt32(xs[0..4]);
    var sqn := SeqToUInt32(xs[4..8]);
    var ivEnd := algorithmSuiteID.IVLength() as uint32 +  8;
    var fl := SeqToUInt32(xs[ivEnd..ivEnd+4]);
    var encryptEnd := 4 + 4 + algorithmSuiteID.IVLength() + 4 + fl as int + algorithmSuiteID.TagLength() as int;
    FinalFrameCons(sqnE,sqn,xs[8..ivEnd],fl,xs[ivEnd+4..encryptEnd],xs[encryptEnd..])
  }

  //Converts sequence of Frames to a sequence encoding all frames
  function FramesToSequence(fs : seq<Frame>): (xs: seq<uint8>)
    requires |fs| <= UINT32_LIMIT
  {
    if fs == [] then
      []
    else
      FrameToSubsequence(fs[0]) + FramesToSequence(fs[1..])
  }

  //Converts Frame to a sequence encoding a frame
  function FrameToSubsequence(f : Frame): (xs: seq<uint8>)
    ensures |xs| <= UINT32_LIMIT
  {
    match f 
      case RegFrameCons(seqNumb, iv, encCont, authTag) =>
        var seqNumSeq := UInt32ToSeq(seqNumb);
        seqNumSeq + iv + encCont + authTag

      case FinalFrameCons(seqNumbEnd, seqNumb, iv, encContLength, encCont, authTag) =>
        var seqNumbEndSeq := UInt32ToSeq(seqNumbEnd);
        var seqNumbSeq := UInt32ToSeq(seqNumb);
        var encContLengthSeq := seq(4 - |UInt32ToSeq(encContLength)|, _ => 0) + UInt32ToSeq(encContLength);
        seqNumbEndSeq + seqNumbSeq + iv + encContLengthSeq + encContLengthSeq + authTag
  }


  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID) returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    requires frameLength > 0
    ensures match res
      case Failure(e) => true
      case Success(resS) => exists fs: seq<Frame> :: 
           0 < |fs| < UINT32_LIMIT    
        && FramesToSequence(fs) == resS
        && fs[|fs| - 1].FinalFrameCons?
        && 0 <= fs[|fs|-1].encContLength as int <= frameLength 
        && forall f | f in fs[..|fs| - 1] :: f.RegFrameCons?
        && forall f | f in fs[..|fs| - 1] :: frameLength == |f.encCont|
        && fs[0].seqNumb == 1
        && fs[|fs|-1].seqNumbEnd as int == |fs|
        && forall i | 0 <= i < |fs| - 1 :: fs[i+1].seqNumb as int == fs[i].seqNumb as int + 1
        && forall f1,f2 | f1 in fs && f2 in fs && f1 != f2 :: f1.iv != f2.iv
        && |plaintext| < frameLength ==> |fs| == 1 && fs[0].FinalFrameCons?  
  { 
    var body := [];
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    
    ghost var fres : seq<Frame> := [];
    
    while n + frameLength < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure("too many frames");
      }
      var plaintextFrame := plaintext[n..n + frameLength];
      var regularFrame :- EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      
      fres := fres + [SubsequenceToRegFrame(regularFrame, algorithmSuiteID, frameLength)];
      body := body + regularFrame;
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
    }

    var finalFrame :- EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    body := body + finalFrame;
    
    fres := fres + [SubsequenceToFinalFrame(finalFrame, algorithmSuiteID, frameLength)];
    
    return Success(body);
  }

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, ghost frameLength: int,
                             messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res 
      case Failure(e) => true
      case Success(resS) => 
        |resS| == 4 + algorithmSuiteID.IVLength() + frameLength + algorithmSuiteID.TagLength() &&
        var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
        var encCont := resS[4 + algorithmSuiteID.IVLength() ..4 + algorithmSuiteID.IVLength() + frameLength]; //Is there a better way to do this
        var authTag := resS[4 + algorithmSuiteID.IVLength() + frameLength..];
        var frame := RegFrameCons(sequenceNumber, iv, encCont, authTag);
        FrameToSubsequence(frame) == resS
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;

    var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;

    var aad := BodyAAD(messageID, RegularFrame, sequenceNumber, |plaintext| as uint64);

    var encryptionOutput :- AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

    return Success(unauthenticatedFrame);
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int,
                           messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| <= frameLength
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res 
      case Failure(e) => true
      case Success(resS) => 
            |resS| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext| + algorithmSuiteID.TagLength()
        &&  |plaintext| == SeqToUInt32(resS[4 + 4 + algorithmSuiteID.IVLength()..4 + 4 + algorithmSuiteID.IVLength() + 4]) as int &&
        var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
        var encCont := resS[4 + 4 + algorithmSuiteID.IVLength() + 4 .. 4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext|]; //Is there a better way to do this
        var authTag := resS[4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext|..];
        var frame := FinalFrameCons(ENDFRAME_SEQUENCE_NUMBER, sequenceNumber, iv, |plaintext| as uint32, encCont, authTag);
            FrameToSubsequence(frame) == resS
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
    
    return Success(unauthenticatedFrame);
  }

  method DecryptFramedMessageBody(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID) returns (res: Result<seq<uint8>>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
  {
    var plaintext := [];
    var n := 1;
    while true
      invariant rd.Valid()
      decreases ENDFRAME_SEQUENCE_NUMBER - n
    {
      var pair :- DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, n);
      var (framePlaintext, final) := pair;
      plaintext := plaintext + framePlaintext;
      if final {
        break;
      }
      n := n + 1;
    }
    return Success(plaintext);
  }

  method DecryptFrame(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID,
                      expectedSequenceNumber: uint32)
      returns (res: Result<(seq<uint8>, bool)>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res
      case Success((plaintext, final)) =>
        expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> final  // but "final" may come up before this
      case Failure(_) => true
  {
    var final := false;
    var sequenceNumber :- rd.ReadUInt32();
    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
    }
    if sequenceNumber != expectedSequenceNumber {
      return Failure("unexpected frame sequence number");
    }

    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());

    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
    }

    var aad := BodyAAD(messageID, if final then FinalFrame else RegularFrame, sequenceNumber, len as uint64);

    var ciphertext :- rd.ReadBytes(len as nat);
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);

    return Success((plaintext, final));
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
}
