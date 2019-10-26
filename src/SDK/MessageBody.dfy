include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "MessageHeader.dfy"
include "AlgorithmSuite.dfy"
include "../Crypto/AESEncryption.dfy"

module MessageBody {
  export
    provides EncryptMessageBody
    provides StandardLibrary, UInt, Msg, AlgorithmSuite

  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Msg = MessageHeader
  import AESEncryption

  const BODY_AAD_CONTENT_REGULAR_FRAME := StringToByteSeq("AWSKMSEncryptionClient Frame");
  const BODY_AAD_CONTENT_FINAL_FRAME := StringToByteSeq("AWSKMSEncryptionClient Final Frame");

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 0xFFFF_FFFF

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID) returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
  {
    var body := [];
    var n, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    while n + frameLength <= |plaintext|
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

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int,
                             messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber as uint32);
    var unauthenticatedFrame := seqNumSeq;

    var iv: seq<uint8> := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber as uint32);
    assert |iv| == algorithmSuiteID.IVLength();
    unauthenticatedFrame := unauthenticatedFrame + iv;

    var contentAAD := BODY_AAD_CONTENT_REGULAR_FRAME;
    var aad := messageID + contentAAD + seqNumSeq + UInt64ToSeq(|plaintext| as uint64);

    var encryptionOutput :- Encrypt(algorithmSuiteID, iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

    return Success(unauthenticatedFrame);
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int,
                           messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| < frameLength
    requires 4 <= algorithmSuiteID.IVLength()
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber as uint32);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;

    var iv: seq<uint8> := seq(algorithmSuiteID.IVLength() - 4, _ => 0) + UInt32ToSeq(sequenceNumber as uint32);
    assert |iv| == algorithmSuiteID.IVLength();
    unauthenticatedFrame := unauthenticatedFrame + iv;

    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);

    var contentAAD := BODY_AAD_CONTENT_FINAL_FRAME;
    var aad := messageID + contentAAD + seqNumSeq + UInt64ToSeq(|plaintext| as uint64);

    var encryptionOutput :- Encrypt(algorithmSuiteID, iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;

    return Success(unauthenticatedFrame);
  }

  method Encrypt(algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, plaintext: seq<uint8>, aad: seq<uint8>) returns (res: Result<AESEncryption.EncryptionOutput>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    ensures match res
      case Success(encryptionOutput) =>
        |encryptionOutput.cipherText| == |plaintext| &&
        |encryptionOutput.authTag| == algorithmSuiteID.TagLength()
      case Failure(_) => true
  {
    var cipher := AlgorithmSuite.Suite[algorithmSuiteID].algorithm;
    var encryptionOutput :- AESEncryption.AESEncrypt(cipher, iv, key, plaintext, aad);
    return Success(encryptionOutput);
  }
}
