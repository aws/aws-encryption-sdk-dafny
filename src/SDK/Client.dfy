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

  class EncryptorStream extends Collections.ByteProducer {
    // TODO having issues with extern constructors
    //constructor(bytes: seq<uint8>) {}
    // The top level one shouldn't actually have to deal with internal buffers
    var inStream: Streams.InputStream
    var index: int
    // TODO have to declare here if we want verification around it. Brittle.
    var cmm: CMMDefs.CMM
    var optEncryptionContext: Option<Materials.EncryptionContext>
    var algorithmSuiteID: Option<AlgorithmSuite.ID>
    var optFrameLength: Option<uint32>
    var length: int32
    var downStream: MessageHeaderStream

    predicate Valid() reads this ensures Valid() ==> this in Repr {
      // TODO check downstream is valid?
      && this in Repr
    }

    constructor(inStream: Streams.InputStream, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>)
      ensures fresh(Repr - {this})
    {
      // TODO most all of this stuff is just needed to pass down to MessageHeaderStream.
      // It would be better to create that outside this and compose them together?
      // Or should this be responsible for creating and composing all sub streams?
      this.Repr := {this};
      this.inStream := inStream;
      this.cmm := cmm;
      this.optEncryptionContext := optEncryptionContext;
      this.algorithmSuiteID := algorithmSuiteID;
      this.optFrameLength := optFrameLength;
      this.downStream := new MessageHeaderStream(inStream, cmm, optEncryptionContext, algorithmSuiteID, optFrameLength);
    }

    // TODO Not sure how this should fit together...
    method HasNext() returns (b: bool)
      requires Valid()
      ensures Valid()
    {
      b := downStream.HasNext();
    }

    method Next() returns (res: Result<uint8>) 
      requires Valid()
      //requires HasNext()
      ensures Valid()
      modifies this
    {
      // TODO This is brittle, HasNext can't guarantee that this will succeed,
      // especially since we might experience a failure in a transformation done
      // in the downstream. Right now failures and EOF are propogating up as 0.
      res := downStream.Next();
    }

    method Siphon(consumer: Collections.ByteConsumer) returns (siphoned: Result<int>) 
      requires Valid()
      requires consumer.Valid()
      requires this !in consumer.Repr
      requires consumer !in Repr
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      // Use default siphon. Is there a subtype check we could be making here
      // to improve performance in certain cases?
      siphoned := Collections.DefaultSiphon(this, consumer);
    }
  }

  class MessageHeaderStream extends Collections.ByteProducer {
    // TODO having issues with extern constructors
    //constructor(bytes: seq<uint8>) {}
    var inStream: Streams.InputStream
    var inBuffer: seq<uint8> // Use the byteReader/Writer?
    var outBuffer: seq<uint8>
    var cmm: CMMDefs.CMM
    var optEncryptionContext: Option<Materials.EncryptionContext>
    var algorithmSuiteID: Option<AlgorithmSuite.ID>
    var optFrameLength: Option<uint32>
    var length: int32
    var didTheThing: bool
    var downStream: EncryptTheRestStream

    predicate Valid() reads this ensures Valid() ==> this in Repr {
      // TODO check downstream Valid?
      && this in Repr
    }

    constructor(inStream: Streams.InputStream, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>) {
      this.inStream := inStream;
      this.cmm := cmm;
      this.optEncryptionContext := optEncryptionContext;
      this.algorithmSuiteID := algorithmSuiteID;
      this.optFrameLength := optFrameLength;
      this.inBuffer := [];
      this.outBuffer := [];
      this.didTheThing := false;
      this.downStream := new EncryptTheRestStream(inStream, cmm, optEncryptionContext, algorithmSuiteID, optFrameLength);
    }

    // TODO Not sure how this should fit together...
    method HasNext() returns (b: bool)
      requires Valid()
      ensures Valid()
    {
      b := downStream.HasNext();
    }

    method Next() returns (res: Result<uint8>) 
      requires Valid()
      //requires HasNext()
      ensures Valid()
      modifies this
    {
      // serialize the message header with our info on first read.
      if !didTheThing {
        var _ :- FillOutBuffer();
        // we did the thing, so flip the bool so we don't do it again.
        didTheThing := true;
        expect |outBuffer| > 0;
      }
      // if we have stuff in the outBuffer. Take from that.
      if |outBuffer| > 0 {
        var byte := outBuffer[0];
        // TODO will this grab correctly in the case that |outBuffer| == 1?
        outBuffer := outBuffer[1..];
        return Success(byte);
      }
      // if we don't have anything in the outBuffer and we did the thing, then
      // that means we need to send to the next streaming interface in order
      // to deal with the actual encryption
      res := downStream.Next();
    }

    method Siphon(consumer: Collections.ByteConsumer) returns (siphoned: Result<int>) 
      requires Valid()
      requires consumer.Valid()
      requires this !in consumer.Repr
      requires consumer !in Repr
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      // Use default siphon. Is there a subtype check we could be making here
      // to improve performance in certain cases?
      siphoned := Collections.DefaultSiphon(this, consumer);
    }

    // We don't actually have to read anything from the input stream
    // in order to make the header.
    // Call this the first time the stream is read.
    // TODO make this foolproof
    // TODO remove Result<bool> :P
    method FillOutBuffer() returns (res: Result<bool>) {
      var encryptionContext := optEncryptionContext.GetOrElse(map[]);
      assert Msg.ValidAAD(encryptionContext) by {
        reveal Msg.ValidAAD();
        assert Msg.ValidAAD(encryptionContext);
      }
      var frameLength := if optFrameLength.Some? then optFrameLength.get else DEFAULT_FRAME_LENGTH;
      
      // This assumes inStream is seekable :/
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
      outBuffer := wr.GetDataWritten();

      // TODO better way to do this
      downStream.SetDerivedValues(outBuffer, headerBody, derivedDataKey, encMat);
      return Success(true);
    }
  }

  // For now this stream just fills the rest of the buffer with the input stream,
  // then encrypts that plaintext.
  // This should be broken into parts so that it is not necessary to fill then entire
  // plaintext/ciphertext into memory. But right now we're focusing on the streaming
  // interface.
  class EncryptTheRestStream extends Collections.ByteProducer {
    // TODO having issues with extern constructors
    //constructor(bytes: seq<uint8>) {}
    var inStream: Streams.InputStream
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

    predicate Valid() reads this ensures Valid() ==> this in Repr {
      // TODO check downstream Valid?
      && this in Repr
    }

    // more woof.
    constructor(inStream: Streams.InputStream, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>) {
      this.inStream := inStream;
      this.cmm := cmm;
      this.optEncryptionContext := optEncryptionContext;
      this.algorithmSuiteID := algorithmSuiteID;
      this.optFrameLength := optFrameLength;
      this.inBuffer := [];
      this.outBuffer := [];
    }

    method SetDerivedValues(serHeader: seq<uint8>, header: Msg.HeaderBody, dataKey: seq<uint8>, encMat: Materials.EncryptionMaterials)
    {
      this.serHeader := serHeader;
      this.header := header;
      this.encMat := encMat;
      this.dataKey := dataKey;
    }

    // TODO Better way to do this...
    method HasNext() returns (b: bool)
      requires Valid()
      ensures Valid()
    {
      // :'(
      var pos := inStream.Position();
      var len := inStream.Length();
      return !(pos == len && |outBuffer| == 0);
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
      // Read from input stream until we get enough where we can output something
      // (which right now means read everything :P)
      var len := inStream.Length();
      var bytesInput: seq<uint8> := seq(1, _ => 0);
      while |inBuffer| < len as int {
        // This is assuming inStream is a C# streaming interface
        var n := inStream.Read(bytesInput, 0, 1);
        // we've reached the end of the input stream! This shouldn't happen unless we were wrong
        // about len :/
        if n == 0 {
          // This shouldn't happen because this method can only be called
          // if inStream.Position != inStream.Length
          // If it does anyway, :shrug: return 0.
          // FIXME
          return Success(0);
        }
        // If not 0 it MUST be 1
        expect n == 1;
        // TODO this way of adding byte by byte will be REALLY slow. But simpifying implementation
        // for now by assuming that the streaming is byte by byte.
        inBuffer := inBuffer + [bytesInput[0]];
        // So we have some more input, but do we have enough so that we can output a byte?
        // For now, we can't output anything until we input everything.
        // If we've buffered everything into memory, do the whole encryption
        // TODO Will we always know inStream's length? No, what do we do in that case?
      }
      // if we're going byte by byte this MUST be true
      // we've loaded all the plaintext into the inBuffer
      expect |inBuffer| == len as int;

      // Time to do the actual encryption
      // Encrypt the given plaintext into the message body and add a footer with a signature, if required
      var body :- MessageBody.EncryptMessageBody(inBuffer, header.frameLength as int, header.messageID, dataKey, encMat.algorithmSuiteID);
      var msg := serHeader + body;

      match encMat.algorithmSuiteID.SignatureType() {
        case None =>
          // don't use a footer
        case Some(ecdsaParams) =>
          var digest :- Signature.Digest(ecdsaParams, msg);
          var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
          if |bytes| != ecdsaParams.SignatureLength() as int {
            return Failure("Malformed response from Sign().");
          }
          // TODO this hurt you
          body := body + UInt16ToSeq(|bytes| as uint16) + bytes;
      }
      // Grab the one byte we want to return
      var byte := body[0];
      // Add the rest to the buffer
      // the outBuffer MUST be empty if we were reading from input
      expect |outBuffer| == 0;
      outBuffer := body[1..];
      // consume the inputBuffer
      inBuffer := [];
      return Success(byte); 
    }

    method Siphon(consumer: Collections.ByteConsumer) returns (siphoned: Result<int>) 
      requires Valid()
      requires consumer.Valid()
      requires this !in consumer.Repr
      requires consumer !in Repr
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      // Use default siphon. Is there a subtype check we could be making here
      // to improve performance in certain cases?
      siphoned := Collections.DefaultSiphon(this, consumer);
    }
  }

  method StreamEncrypt(inStream: Streams.InputStream, cmm: CMMDefs.CMM, optEncryptionContext: Option<Materials.EncryptionContext>, algorithmSuiteID: Option<AlgorithmSuite.ID>, optFrameLength: Option<uint32>) returns (res: Result<EncryptorStream>)
    requires cmm.Valid()
    requires optFrameLength.Some? ==> optFrameLength.get != 0
    requires optEncryptionContext.Some? ==> optEncryptionContext.get.Keys !! Materials.ReservedKeyValues && Msg.ValidAAD(optEncryptionContext.get)
    decreases *
  {
    // This should be a composition of them, not some noop stream wrapping them in a stack
    var outStream := new EncryptorStream(inStream, cmm, optEncryptionContext, algorithmSuiteID, optFrameLength);
    //var _ := outStream.FillBuffer(ciphertext);

    return Success(outStream);
    // TODO convert to output stream
  }

/*
  method StreamDecrypt(in: InputStream, cmm: CMMDefs.CMM) returns (res: Result<seq<uint8>>)
  {
    // convert in to message
    return Decrypt(message, cmm);
    // TODO convert to output stream
  }
*/

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
