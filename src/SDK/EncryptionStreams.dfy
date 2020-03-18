include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "../Util/Streams.dfy"
include "../Crypto/Signature.dfy"
include "../StandardLibrary/Collections.dfy"

module {:extern "EncryptionStreams"} EncryptionStreams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Msg = MessageHeader
  import MessageBody
  import Serialize
  import Streams
  import Signature
  import Collections

  // TODO This should probably implement a more generic Stream trait
  class EncryptionStream {
    ghost const Repr: set<object>
    var producer: Collections.ByteProducer
    // TODO If EncryptionStream implements a generic trait, this would have to be the generic
    // ByteConsumer. However, we don't have a good way to get to the bits 'Accept'ed
    // by a ByteConsumer. For now, explicitly use The EncryptionConsumer which
    // has methods to get to the buffered bytes. I'm thinking that maybe
    // we need to pipe two streams together, one which feeds bytes into the encryptor
    // stream, and another which feeds from the encryptor to a ByteConsumer which is
    // controlled by the extern (i.e. the extern could maintain the buffer of the extern 
    // ByteConsumer and siphon from the encryptor to the extern ByteConsumer)
    var consumer: EncryptionConsumer

    predicate Valid()
      reads this, Repr, this.consumer, this.producer, this.producer.Repr
      ensures Valid() ==> this in Repr
    {
      && this.consumer.Valid()
      && this.producer.Valid()
      && this.consumer.Repr !! this.producer.Repr
      && Repr == {this, consumer, producer}
    }

    constructor(producer: Collections.ByteProducer, consumer: EncryptionConsumer) {
      this.Repr := {this, consumer, producer};
      this.producer := producer;
      this.consumer := consumer;
    }

    // TODO This is not the interface we want for getting bytes out of the stream.
    // But is being used currently by shim ClientEncryptionStream to get to the
    // encrypted bytes
    // TODO this probably should return up to a count, not a single byte
    method GetByte() returns (res: Result<Option<uint8>>)
      requires Valid()
      ensures Valid()
      modifies producer, producer.Repr, consumer, consumer.Repr
      decreases *
    {
      while !consumer.HasNext()
        invariant Valid()
        decreases *
      {
        // FIXME verifier is throwing a fit here over modifies clause
        var siphoned :- producer.Siphon(consumer);
        if siphoned == 0 {
          // None means end of stream
          return Success(None());
        }
      }
      var nextByte :- consumer.Next();
      return Success(Some(nextByte));
    }
  }

  // Transforms plaintext into the encrypted message.
  // Note that it is the consumer that is performing the transformation of the
  // plaintext into the message. However, the requirement that we main both an
  // input and output buffer here makes me think that this encapsulation
  // isn't quite correct. Perhaps this logic needs to move entirely into the
  // stream, and the consumer is just a way for the stream to define the
  // buffer it is siphoning the input stream into and has access to.
  class EncryptionConsumer extends Collections.ByteConsumer {
    // TODO use ByteReader/Writer for these internal buffers?
    // TODO I feel like we shouldn't need two buffers here
    // This is a buffer to hold read plaintext which we have not encrypted yet.
    var plaintext: seq<uint8>
    // This is a buffer for the message which has been processed so far
    var processedMessage: seq<uint8>
    var header: Msg.HeaderBody
    var dataKey: seq<uint8>
    var encMat: Materials.EncryptionMaterials
    var seqNum: uint32
    // TODO Because I don't have a great way to figure out if we've reached
    // the end of a stream, right now the logic for determining
    // whether we're encrypting the final frame relies on knowing the
    // total plaintextLength, and tracking how much we've encrypted so far.
    // Note that this also requires that we know the total plaintext length
    // before we begin, which requires either a seekable input stream
    // or requires us to read the whole input into memory before beginning
    var totalLength: int
    var curLength: int
    // TODO If we have signing right now we put the whole message in memory in
    // order to sign it. There should be a better way to do this.
    var toSign: seq<uint8>

    predicate Valid() reads this ensures Valid() ==> this in Repr {
      this in Repr
    }

    // TODO serHeader shouldn't be passed into constructor, but instead passed through the stream
    constructor(serHeader: seq<uint8>, header: Msg.HeaderBody, dataKey: seq<uint8>, encMat: Materials.EncryptionMaterials, totalLength: int)
      requires encMat.algorithmSuiteID.SignatureType().Some? ==> encMat.signingKey.Some?
      requires |dataKey| == encMat.algorithmSuiteID.KeyLength()
    {
      this.plaintext := [];
      this.processedMessage := serHeader;
      this.header := header;
      this.encMat := encMat;
      this.dataKey := dataKey;
      this.seqNum := 1;
      this.totalLength := totalLength;
      this.curLength := 0;
      this.toSign := serHeader;
      this.Repr := {this};
    }

    predicate method CanAccept() reads this, Repr
      requires Valid()
      ensures Valid()
    {
      curLength <= totalLength
    }
    
    // Adds the accepted bit into our input buffer
    // and if enough have been accumulated, process the
    // plaintext into a frame in our output buffer
    method Accept(b: uint8) returns (res: Result<()>)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr
    {
      // Add to plaintext
      plaintext := plaintext + [b];
      // Update total Length
      curLength := curLength + 1;
      var frameLength := header.frameLength;

      // TODO Split regular/final frame logic based on current position in input stream.
      // I don't like this approach, but I think doing something like this is required
      // as long as we do not have control over the number of bytes we are reading from
      // input, and are instead "waiting" to accept some number. See above comment
      // for moving encryption logic elsewhere.
      if totalLength == curLength {
        var frameToProcess := plaintext;
        plaintext := [];
        
        var encryptedFrame :- MessageBody.EncryptFinalFrame(encMat.algorithmSuiteID, dataKey, frameLength as int, header.messageID, frameToProcess, seqNum);
        processedMessage := processedMessage + encryptedFrame;
        toSign := toSign + encryptedFrame;
        // Since we've encrypted the final frame, we can also calculate
        // the footer
        var res :- AddSignatureToProcessedMessage();
      } else if |plaintext| >= frameLength as int {
        var frameToProcess := plaintext[..frameLength];
        plaintext := plaintext[frameLength..];
        var encryptedFrame :- MessageBody.EncryptRegularFrame(encMat.algorithmSuiteID, dataKey, frameLength as int, header.messageID, frameToProcess, seqNum);
        processedMessage := processedMessage + encryptedFrame;
        toSign := toSign + encryptedFrame;
      }
      return Success(());
    }

    method AddSignatureToProcessedMessage() returns (res: Result<bool>)
      requires encMat.algorithmSuiteID.SignatureType().Some? ==> encMat.signingKey.Some?
      modifies this`processedMessage
    {
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
          processedMessage := processedMessage + UInt16ToSeq(|bytes| as uint16) + bytes;
          return Success(true);
      }
    }

    predicate method HasNext()
      reads this
      requires Valid()
      ensures Valid()
    {
      |processedMessage| > 0
    }

    method Next() returns (res: Result<uint8>) 
      requires Valid()
      //requires HasNext()
      ensures Valid()
      modifies this
    {
      // if we have stuff in the processedMessage. Take from that.
      if |processedMessage| > 0 {
        var byte := processedMessage[0];
        // TODO will this grab correctly in the case that |processedMessage| == 1?
        processedMessage := processedMessage[1..];
        return Success(byte);
      }
    }
  }
}
