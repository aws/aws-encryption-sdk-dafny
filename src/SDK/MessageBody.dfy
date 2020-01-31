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
    provides DecryptFramedMessageBody
    provides StandardLibrary, UInt, Msg, AlgorithmSuite, Materials, Streams

  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Msg = MessageHeader
  import AESEncryption
  import Materials
  import Streams
  import EncryptionSuites
  import UTF8

  const AWS_KMS_ENCRYPTION_CLIENT_REGULAR_FRAME := "AWSKMSEncryptionClient Frame";
  method GetBodyAADContentRegularFrame() returns (res: UTF8.ValidUTF8Bytes)
  {
    var encoded := UTF8.Encode(AWS_KMS_ENCRYPTION_CLIENT_REGULAR_FRAME);
    return encoded;
  }

  const AWS_KMS_ENCRYPTION_CLIENT_FINAL_FRAME := "AWSKMSEncryptionClient Final Frame";
  method GetBodyAADContentFinalFrame() returns (res: UTF8.ValidUTF8Bytes)
  {
    var encoded := UTF8.Encode(AWS_KMS_ENCRYPTION_CLIENT_FINAL_FRAME);
    return encoded;
  }

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID) returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
  {
    var body := [];
    var n, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    while n + frameLength < |plaintext|
      invariant 0 <= n <= |plaintext|
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure("too many frames");
      }
      var plaintextFrame := plaintext[n..n + frameLength];
      var regularFrame :- EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      body := body + regularFrame;
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
    }
    var finalFrame :- EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    body := body + finalFrame;
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
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;

    var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;

    var aad := BodyAAD(messageID, false, sequenceNumber, |plaintext| as uint64);

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
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;

    var iv := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);  // this proves SeqToNat(iv) == sequenceNumber as nat
    unauthenticatedFrame := unauthenticatedFrame + iv;

    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);

    var aad := BodyAAD(messageID, true, sequenceNumber, |plaintext| as uint64);

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

    var aad := BodyAAD(messageID, final, sequenceNumber, len as uint64);

    var ciphertext :- rd.ReadBytes(len as nat);
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);

    return Success((plaintext, final));
  }

  method BodyAAD(messageID: seq<uint8>, final: bool, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var bodyAADFinalFrame := GetBodyAADContentFinalFrame();
    var bodyAADRegularFrame := GetBodyAADContentRegularFrame();
    var contentAAD := if final then bodyAADFinalFrame else bodyAADRegularFrame;
    aad := messageID + contentAAD + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(ciphertext: seq<uint8>, authTag: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, aad: seq<uint8>) returns (res: Result<seq<uint8>>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    requires |authTag| == algorithmSuiteID.TagLength()
  {
    var encAlg := algorithmSuiteID.EncryptionSuite();
    res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
  }
}
