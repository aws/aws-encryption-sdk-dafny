include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "CMM/Defs.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "Deserialize.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/KeyDerivationAlgorithms.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"
include "../StandardLibrary/Collections.dfy"

module {:extern "ESDKClient"} ESDKClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import CMMDefs
  import Msg = MessageHeader
  import MessageBody
  import Serialize
  import Random
  import KeyDerivationAlgorithms
  import Streams
  import HKDF
  import AESEncryption
  import Signature
  import Deserialize
  import Collections

  const DEFAULT_FRAME_LENGTH: uint32 := 4096

  // passes through the header and encrypts the plaintext
  // This will read all of the plaintext into memory before
  // performing the encryption because this is a proof of concept
  // for the streaming interface.
  class EncryptTheRestStream extends Collections.ByteConsumer {
    var inBuffer: seq<uint8> // Use the byteReader/Writer?
    var outBuffer: seq<uint8>
    var cmm: CMMDefs.CMM
    var optEncryptionContext: Option<Materials.EncryptionContext>
    var algorithmSuiteID: Option<AlgorithmSuite.ID>
    var optFrameLength: Option<uint32>
    var length: int32
    var serHeader: seq<uint8>
    var header: Msg.HeaderBody
    var dataKey: seq<uint8>
    var encMat: Materials.EncryptionMaterials
    var seqNum: uint32
    var isFinalFrame: bool
    var finished: bool
    var totalLength: int
    var curLength: int
    var toSign: seq<uint8>

    ghost const Repr: set<object>

    predicate Valid() reads this ensures Valid() ==> this in Repr {
      // TODO check downstream Valid?
      && this in Repr
    }

    // more woof.
    constructor(cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>, serHeader: seq<uint8>, header: Msg.HeaderBody, dataKey: seq<uint8>, encMat: Materials.EncryptionMaterials, totalLength: int) {
      this.cmm := cmm;
      this.optEncryptionContext := optEncryptionContext;
      this.algorithmSuiteID := algorithmSuiteID;
      this.optFrameLength := optFrameLength;
      this.inBuffer := [];
      this.outBuffer := serHeader;
      this.serHeader := serHeader;
      this.header := header;
      this.encMat := encMat;
      this.dataKey := dataKey;
      this.seqNum := 1;
      this.isFinalFrame := false;
      this.finished := false;
      this.totalLength := totalLength;
      this.curLength := 0;
      // TODO :(
      this.toSign := serHeader;
    }

    predicate method CanAccept() reads this, Repr
      requires Valid()
      ensures Valid()
    {
      !finished
    }
    
    method Accept(b: uint8) returns (res: Result<()>)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr
    {
      // Add to inBuffer

      inBuffer := inBuffer + [b];

      // TODO update total Length
      curLength := curLength + 1;

      var frameLength := header.frameLength;

      // TODO This is the only way we can know when to encrypt the final frame right now :(
      if totalLength == curLength {
        var frameToProcess := inBuffer;
        inBuffer := [];
        var encryptedFrame :- MessageBody.EncryptFinalFrame(encMat.algorithmSuiteID, dataKey, frameLength as int, header.messageID, frameToProcess, seqNum);
        finished := true;
        outBuffer := outBuffer + encryptedFrame;
        toSign := toSign + encryptedFrame;
        var res :- AddSignatureToOutBuffer();
      } else if |inBuffer| >= frameLength as int {
        var frameToProcess := inBuffer[..frameLength];
        inBuffer := inBuffer[frameLength..];
        var encryptedFrame :- MessageBody.EncryptRegularFrame(encMat.algorithmSuiteID, dataKey, frameLength as int, header.messageID, frameToProcess, seqNum);
        outBuffer := outBuffer + encryptedFrame;
        toSign := toSign + encryptedFrame;
      }
      return Success(());
    }

    method AddSignatureToOutBuffer() returns (res: Result<bool>) {
      match encMat.algorithmSuiteID.SignatureType() {
        case None =>
        return Success(true);
          // don't use a footer
        case Some(ecdsaParams) =>
          var digest :- Signature.Digest(ecdsaParams, toSign);
          var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
          if |bytes| != ecdsaParams.SignatureLength() as int {
            return Failure("Malformed response from Sign().");
          }
          outBuffer := outBuffer + UInt16ToSeq(|bytes| as uint16) + bytes;
          return Success(true);
      }
    }

    predicate method HasNext()
      reads this
      requires Valid()
      ensures Valid()
    {
      |outBuffer| > 0
    }

    method Next() returns (res: Result<uint8>) 
      requires Valid()
      //requires HasNext()
      ensures Valid()
      modifies this
    {
      // if we have stuff in the outBuffer. Take from that.
      if |outBuffer| > 0 {
        var byte := outBuffer[0];
        // TODO will this grab correctly in the case that |outBuffer| == 1?
        outBuffer := outBuffer[1..];
        return Success(byte);
      }
    }
  }

  method StreamEncrypt(inStream: Collections.ExternByteProducer, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>) returns (res: Result<EncryptTheRestStream>)
    requires cmm.Valid()
    requires optFrameLength.Some? ==> optFrameLength.get != 0
    requires optEncryptionContext.Some? ==> optEncryptionContext.get.Keys !! Materials.ReservedKeyValues && Msg.ValidAAD(optEncryptionContext.get)
    decreases *
  {
    // create  header and related values
    var encryptionContext := optEncryptionContext.GetOrElse(map[]);
    assert Msg.ValidAAD(encryptionContext) by {
      reveal Msg.ValidAAD();
      assert Msg.ValidAAD(encryptionContext);
    }
    var frameLength := if optFrameLength.Some? then optFrameLength.get else DEFAULT_FRAME_LENGTH;
      
    // This assumes inStream is seekable :/
    // Should return None if not seekable?
    var len := inStream.Length();
    var encMatRequest := Materials.EncryptionMaterialsRequest(encryptionContext, algorithmSuiteID, Some(len as nat));
    var encMat :- cmm.GetEncryptionMaterials(encMatRequest);
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure("Number of EDKs exceeds the allowed maximum.");
    }

    var messageID: Msg.MessageID :- Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.get, encMat.algorithmSuiteID, messageID);

    // Assemble and serialize the header and its authentication tag
    var headerBody := Msg.HeaderBody(
      Msg.VERSION_1,
      Msg.TYPE_CUSTOMER_AED,
      encMat.algorithmSuiteID,
      messageID,
      encMat.encryptionContext,
      Msg.EncryptedDataKeys(encMat.encryptedDataKeys),
      Msg.ContentType.Framed,
      encMat.algorithmSuiteID.IVLength() as uint8,
      frameLength);
    var wr := new Streams.ByteWriter();

    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();

    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);

    var data := wr.GetDataWritten();
    // This should be a composition of them, not some noop stream wrapping them in a stack
    // Should have header be ingested into finalStream, right now just passing it to constructor :/
    var finalStream := new EncryptTheRestStream(cmm, optEncryptionContext, algorithmSuiteID, optFrameLength, data, headerBody, derivedDataKey, encMat, len as int);
    //var _ := outStream.FillBuffer(ciphertext);
    
    // TODO some way to have a "composed" stream

    return Success(finalStream);
    // TODO convert to output stream
  }

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(plaintext: seq<uint8>, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>) returns (res: Result<seq<uint8>>)
    requires cmm.Valid()
    requires optFrameLength.Some? ==> optFrameLength.get != 0
    requires optEncryptionContext.Some? ==> optEncryptionContext.get.Keys !! Materials.ReservedKeyValues && Msg.ValidAAD(optEncryptionContext.get)
  {
    var encryptionContext := optEncryptionContext.GetOrElse(map[]);
    assert Msg.ValidAAD(encryptionContext) by {
      reveal Msg.ValidAAD();
      assert Msg.ValidAAD(encryptionContext);
    }
    var frameLength := if optFrameLength.Some? then optFrameLength.get else DEFAULT_FRAME_LENGTH;
    
    var encMatRequest := Materials.EncryptionMaterialsRequest(encryptionContext, algorithmSuiteID, Some(|plaintext|));
    var encMat :- cmm.GetEncryptionMaterials(encMatRequest);
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure("Number of EDKs exceeds the allowed maximum.");
    }

    var messageID: Msg.MessageID :- Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.get, encMat.algorithmSuiteID, messageID);

    // Assemble and serialize the header and its authentication tag
    var headerBody := Msg.HeaderBody(
      Msg.VERSION_1,
      Msg.TYPE_CUSTOMER_AED,
      encMat.algorithmSuiteID,
      messageID,
      encMat.encryptionContext,
      Msg.EncryptedDataKeys(encMat.encryptedDataKeys),
      Msg.ContentType.Framed,
      encMat.algorithmSuiteID.IVLength() as uint8,
      frameLength);
    var wr := new Streams.ByteWriter();

    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();

    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);

    // Encrypt the given plaintext into the message body and add a footer with a signature, if required
    var body :- MessageBody.EncryptMessageBody(plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);
    var msg := wr.GetDataWritten() + body;

    match encMat.algorithmSuiteID.SignatureType() {
      case None =>
        // don't use a footer
      case Some(ecdsaParams) =>
        var digest :- Signature.Digest(ecdsaParams, msg);
        var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
        if |bytes| != ecdsaParams.SignatureLength() as int {
          return Failure("Malformed response from Sign().");
        }
        msg := msg + UInt16ToSeq(|bytes| as uint16) + bytes;
    }

    return Success(msg);
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID) returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
  {
    var algorithm := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if algorithm == KeyDerivationAlgorithms.IDENTITY {
      return plaintextDataKey;
    }

    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;

    var len := algorithmSuiteID.KeyLength();

    var derivedKey := HKDF.Hkdf(algorithm, None, plaintextDataKey, infoSeq, len);
    return derivedKey;
  }

 /*
  * Deserialize a message and decrypt into a plaintext.
  */
  method Decrypt(message: seq<uint8>, cmm: CMMDefs.CMM) returns (res: Result<seq<uint8>>)
    requires cmm.Valid()
  {
    var rd := new Streams.ByteReader(message);
    var header :- Deserialize.DeserializeHeader(rd);
    var decMatRequest := Materials.DecryptionMaterialsRequest(header.body.algorithmSuiteID, header.body.encryptedDataKeys.entries, header.body.aad);
    var decMat :- cmm.DecryptMaterials(decMatRequest);

    var decryptionKey := DeriveKey(decMat.plaintextDataKey.get, decMat.algorithmSuiteID, header.body.messageID);

    // Parse and decrypt the message body
    var plaintext;
    match header.body.contentType {
      case NonFramed =>
        plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.messageID);
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.frameLength as int, header.body.messageID);
    }

    match decMat.algorithmSuiteID.SignatureType() {
      case None =>
        // there's no footer
      case Some(ecdsaParams) =>
        var usedCapacity := rd.GetSizeRead();
        assert usedCapacity <= |message|;
        var msg := message[..usedCapacity];  // unauthenticatedHeader + authTag + body  // TODO: there should be a better way to get this
        // read signature
        var signatureLength :- rd.ReadUInt16();
        var sig :- rd.ReadBytes(signatureLength as nat);
        // verify signature
        var digest :- Signature.Digest(ecdsaParams, msg);
        var signatureVerified :- Signature.Verify(ecdsaParams, decMat.verificationKey.get, digest, sig);
        if !signatureVerified {
          return Failure("signature not verified");
        }
    }

    var isDone := rd.IsDoneReading();
    if !isDone {
      return Failure("message contains additional bytes at end");
    }

    return Success(plaintext);
  }
}
