// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "EncryptionContext.dfy"
include "CMM/Defs.dfy"
include "CMM/DefaultCMM.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "Deserialize.dfy"
include "Keyring/Defs.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/KeyDerivationAlgorithms.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"

module {:extern "ESDKClient"} ESDKClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionContext
  import AlgorithmSuite
  import AESEncryption
  import CMMDefs
  import DefaultCMMDef
  import Deserialize
  import HKDF
  import KeyringDefs
  import KeyDerivationAlgorithms
  import Materials
  import Msg = MessageHeader
  import MessageBody
  import Random
  import Serialize
  import Signature
  import Streams

  const DEFAULT_FRAME_LENGTH: uint32 := 4096

  datatype EncryptRequest = EncryptRequest(
    plaintext: seq<uint8>,
    cmm: CMMDefs.CMM?,
    keyring: KeyringDefs.Keyring?,
    plaintextLength: nat,
    encryptionContext: EncryptionContext.Map,
    algorithmSuiteID: Option<uint16>,
    frameLength: Option<uint32>)
  {
    static function method WithCMM(plaintext: seq<uint8>, cmm: CMMDefs.CMM): EncryptRequest
      requires cmm.Valid()
      reads cmm.Repr
    {
      EncryptRequest(plaintext, cmm, null, |plaintext|, map[], None, None)
    }

    static function method WithKeyring(plaintext: seq<uint8>, keyring: KeyringDefs.Keyring): EncryptRequest
      requires keyring.Valid()
      reads keyring.Repr
    {
      EncryptRequest(plaintext, null, keyring, |plaintext|, map[], None, None)
    }

    function method SetEncryptionContext(encryptionContext: EncryptionContext.Map): EncryptRequest {
      this.(encryptionContext := encryptionContext)
    }

    function method SetAlgorithmSuiteID(algorithmSuiteID: uint16): EncryptRequest {
      this.(algorithmSuiteID := Some(algorithmSuiteID))
    }

    function method SetFrameLength(frameLength: uint32): EncryptRequest {
      this.(frameLength := Some(frameLength))
    }
  }

  datatype DecryptRequest = DecryptRequest(message: seq<uint8>, cmm: CMMDefs.CMM?, keyring: KeyringDefs.Keyring?)
  {
    static function method WithCMM(message: seq<uint8>, cmm: CMMDefs.CMM): DecryptRequest
      requires cmm.Valid()
      reads cmm.Repr
    {
      DecryptRequest(message, cmm, null)
    }

    static function method WithKeyring(message: seq<uint8>, keyring: KeyringDefs.Keyring): DecryptRequest
      requires keyring.Valid()
      reads keyring.Repr
    {
      DecryptRequest(message, null, keyring)
    }
  }

  // Specification of Encrypt with signature
  function SerializeMessageWithSignature(headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication, frames: seq<MessageBody.Frame>,
      signature: seq<uint8>): (message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
    requires |signature| < UINT16_LIMIT
  {
      var serializedSignature := UInt16ToSeq(|signature| as uint16) + signature;
      SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames) + serializedSignature
  }

  // Specification of Encrypt without signature
  function SerializeMessageWithoutSignature(headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication,frames: seq<MessageBody.Frame>): 
      (message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
  {
      var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
      var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag;
      var serializedFrames := MessageBody.FramesToSequence(frames);
      serializedHeaderBody + serializedHeaderAuthentication + serializedFrames
  }

  // Specification of headerBody in Encrypt
  predicate ValidHeaderBodyForRequest(headerBody: Msg.HeaderBody, request: EncryptRequest)
  {
    headerBody.Valid()
    && headerBody.version == Msg.VERSION_1
    && headerBody.typ == Msg.TYPE_CUSTOMER_AED
    && (exists material: Materials.ValidEncryptionMaterials | CMMDefs.EncryptionMaterialsSignature(material) ::
      headerBody.algorithmSuiteID == material.algorithmSuiteID
      && headerBody.aad == material.encryptionContext
      && headerBody.encryptedDataKeys == Msg.EncryptedDataKeys(material.encryptedDataKeys))
    && headerBody.contentType == Msg.ContentType.Framed
    && headerBody.frameLength == if request.frameLength.Some? then request.frameLength.get else DEFAULT_FRAME_LENGTH
  }

  // Specification of headerAuthentication in Encrypt
  predicate ValidHeaderAuthenticationForRequest(headerAuthentication: Msg.HeaderAuthentication, headerBody: Msg.HeaderBody)
    requires headerBody.Valid()
  {
    var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), _ => 0)
    && Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody)
    && exists encryptionOutput: AESEncryption.EncryptionOutput, cipherkey: seq<uint8> | 
      IsDerivedKey(cipherkey) :: AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, cipherkey)
  }

  // Specification of the Frames used in Encrypt
  predicate ValidFramesForRequest(frames: seq<MessageBody.Frame>, request: EncryptRequest, headerBody: Msg.HeaderBody)
  {
    (forall frame: MessageBody.Frame | frame in frames :: frame.Valid()) //This predicates ensure that the frame can be converted to a sequence
    && MessageBody.FramesEncryptPlaintext(frames, request.plaintext) // This requirement is missing in spec but needed for now needs to be addapted to match streaming
    && (forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == headerBody.algorithmSuiteID.IVLength())
    && (exists cipherkey | IsDerivedKey(cipherkey) :: // The cipherkey used in the encryption is the derived key
       (forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, cipherkey)))
  }

  //Specification of the Signature used in Encrypt
  predicate ValidSignatureForRequest(signature: seq<uint8>, headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication,frames: seq<MessageBody.Frame>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
  {
    var serializedMessage := SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames);
    |signature| < UINT16_LIMIT
    && (exists material: Materials.ValidEncryptionMaterials | CMMDefs.EncryptionMaterialsSignature(material) && material.signingKey.Some? ::
        Signature.IsSigned(material.signingKey.get, serializedMessage, signature))
  }

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(request: EncryptRequest) returns (res: Result<seq<uint8>>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
    modifies if request.cmm == null then {} else request.cmm.Repr
    modifies if request.keyring == null then {} else request.keyring.Repr
    ensures request.cmm != null ==> request.cmm.Valid()
    ensures request.cmm != null ==> fresh(request.cmm.Repr - old(request.cmm.Repr))
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.algorithmSuiteID.Some? && request.algorithmSuiteID.get !in AlgorithmSuite.VALID_IDS ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.get == 0 ==> res.Failure?
    ensures match res 
      case Failure(e) => true
      case Success(encryptedSequence) =>
        // The result is a serialization of 3 items with a potential fourth item. Every item has to meet some specification which is specified in its respective section
        exists headerBody, headerAuthentication, frames | // Some items exists
          ValidHeaderBodyForRequest(headerBody, request) // Which meet their respecive specifications
          && ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody)
          && ValidFramesForRequest(frames, request, headerBody) ::  
            (headerBody.algorithmSuiteID.SignatureType().Some? ==> // If the result needs to be signed then there exists a fourth item 
              exists signature | ValidSignatureForRequest(signature, headerBody, headerAuthentication, frames) :: // which meets its specification
                encryptedSequence == SerializeMessageWithSignature(headerBody, headerAuthentication, frames, signature)) // These items can be serialized to the output
            && headerBody.algorithmSuiteID.SignatureType().None? ==> // if the result does not need to be signed
               encryptedSequence == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames) // Then these items can be serialized to the output
  {
    if request.cmm != null && request.keyring != null {
      return Failure("EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both).");
    } else if request.cmm == null && request.keyring == null {
      return Failure("EncryptRequest.cmm and EncryptRequest.keyring cannot both be null.");
    } else if request.algorithmSuiteID.Some? && request.algorithmSuiteID.get !in AlgorithmSuite.VALID_IDS {
      return Failure("Invalid algorithmSuiteID.");
    } else if request.frameLength.Some? && request.frameLength.get == 0 {
      return Failure("Request frameLength must be > 0");
    }
    var cmm: CMMDefs.CMM;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }

    var frameLength := if request.frameLength.Some? then request.frameLength.get else DEFAULT_FRAME_LENGTH;

    var algorithmSuiteID := if request.algorithmSuiteID.Some? then Some(request.algorithmSuiteID.get as AlgorithmSuite.ID) else None;

    var encMatRequest := Materials.EncryptionMaterialsRequest(request.encryptionContext, algorithmSuiteID, Some(request.plaintextLength as nat));

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
    assert ValidHeaderBodyForRequest (headerBody, request);
    ghost var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    
    var wr := new Streams.ByteWriter();
    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();
    assert unauthenticatedHeader == serializedHeaderBody;
    
    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncryptExtern(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    
    assert ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody) by{
      assert headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), _ => 0);
      assert Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody);
      assert IsDerivedKey(derivedDataKey) && AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, derivedDataKey);
    }
    ghost var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag; 
    
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);
    assert wr.GetDataWritten() == serializedHeaderBody + serializedHeaderAuthentication;
    
    // Encrypt the given plaintext into the message body and add a footer with a signature, if required
    var seqWithGhostFrames :- MessageBody.EncryptMessageBody(request.plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);
    var body := seqWithGhostFrames.sequence;
    ghost var frames := seqWithGhostFrames.frames;
    
    assert ValidFramesForRequest(frames, request, headerBody) && body == MessageBody.FramesToSequence(frames) by {
      assert forall frame: MessageBody.Frame | frame in frames :: frame.Valid();
      assert MessageBody.FramesEncryptPlaintext(frames, request.plaintext); // This requirement is missing in spec but needed
      assert forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == headerBody.algorithmSuiteID.IVLength();
      assert IsDerivedKey(derivedDataKey); 
      assert forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, derivedDataKey);
    }

    var msg := wr.GetDataWritten() + body;
    if encMat.algorithmSuiteID.SignatureType().Some? {
      var ecdsaParams := encMat.algorithmSuiteID.SignatureType().get;
      var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, msg);
      if |bytes| != ecdsaParams.SignatureLength() as int {
        return Failure("Malformed response from Sign().");
      }
      var signature := UInt16ToSeq(|bytes| as uint16) + bytes; 
      assert ValidSignatureForRequest(bytes, headerBody, headerAuthentication, frames) by{
        assert |signature| < UINT16_LIMIT;
        assert Signature.IsSigned(encMat.signingKey.get, msg, bytes)  ;
      }
      msg := msg + signature; 
      assert headerBody.algorithmSuiteID.SignatureType().Some?;
      assert msg == SerializeMessageWithSignature(headerBody, headerAuthentication, frames, bytes);
      return Success(msg);
    } else {
      // don't use a footer
      assert msg == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames);
      return Success(msg);
    }
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID) returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
    ensures IsDerivedKey(derivedDataKey)
  {
    var algorithm := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if algorithm == KeyDerivationAlgorithms.IDENTITY {
      assert IsDerivedKey(plaintextDataKey) by {
        reveal IsDerivedKey();
      }
      return plaintextDataKey;
    }

    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.Hkdf(algorithm, None, plaintextDataKey, infoSeq, len);
    assert IsDerivedKey(derivedKey) by {
      reveal IsDerivedKey();
    }
    return derivedKey;
  }

  predicate {:opaque} IsDerivedKey(derivedDataKey: seq<uint8>)
  {
    true
  }

  method Decrypt(request: DecryptRequest) returns (res: Result<seq<uint8>>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
    modifies if request.cmm == null then {} else request.cmm.Repr
    modifies if request.keyring == null then {} else request.keyring.Repr
    ensures request.cmm != null ==> request.cmm.Valid()
    ensures request.cmm != null ==> fresh(request.cmm.Repr - old(request.cmm.Repr))
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
  {
    var decryptWithVerificationInfo :- DecryptWithVerificationInfo(request);
    return Success(decryptWithVerificationInfo.plaintext);
  }

  datatype DecryptResultWithVerificationInfo = 
    DecryptResultWithVerificationInfo(plaintext: seq<uint8>, ghost header: Msg.Header, ghost hbSeq: seq<uint8>, ghost frames: seq<MessageBody.Frame>, ghost signature: seq<uint8>)

  // Verification of this method requires verification of the CMM to some extend, The verification of the Decrypt method should be extended after CMM is verified
  method DecryptWithVerificationInfo(request: DecryptRequest) returns (res: Result<DecryptResultWithVerificationInfo>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
    modifies if request.cmm == null then {} else request.cmm.Repr
    modifies if request.keyring == null then {} else request.keyring.Repr
    ensures request.cmm != null ==> request.cmm.Valid()
    ensures request.cmm != null ==> fresh(request.cmm.Repr - old(request.cmm.Repr))
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures match res 
      case Failure(e) => true
      case Success(decryptResultWithVerificationInfo) =>
        var header := decryptResultWithVerificationInfo.header;
        var hbSeq := decryptResultWithVerificationInfo.hbSeq;
        var frames := decryptResultWithVerificationInfo.frames;
        var signature := decryptResultWithVerificationInfo.signature;
        && header.body.Valid()
        && Msg.SeqToHeaderBody(hbSeq, header.body)
        && header.body.contentType.Framed? ==> // We only verify framed content for now
          && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid())
          && ((  
            && |signature| < UINT16_LIMIT  
            && request.message == hbSeq + header.auth.iv + header.auth.authenticationTag // These items can be serialized to the output
              + MessageBody.FramesToSequence(frames) + UInt16ToSeq(|signature| as uint16) + signature 
          ) || ( // Weather a message should have a signature depends on the CMM this post condition should be strengthened in the future
            request.message ==  hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames) // if the result does not need to be signed
          ))
  {
    if request.cmm != null && request.keyring != null {
      return Failure("DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
    } else if request.cmm == null && request.keyring == null {
      return Failure("DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");
    }

    var cmm: CMMDefs.CMM;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }

    var rd := new Streams.ByteReader(request.message);
    var deserializeHeaderResult :- Deserialize.DeserializeHeader(rd);
    var header := deserializeHeaderResult.header;
    
    if header.body.contentType.Framed? {
      assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..rd.reader.pos]) by {
        reveal HeaderBySequence();
        assert header.body.contentType.Framed?;
        assert header.body.Valid();
        assert Msg.SeqToHeaderBody(deserializeHeaderResult.hbSeq, header.body);
        assert rd.reader.data[..rd.reader.pos] == deserializeHeaderResult.hbSeq + header.auth.iv + header.auth.authenticationTag;
      }
      assert DataIsFramed(request.message) by {
        assert 0 <= rd.reader.pos <= |request.message|;
        assert rd.reader.data[..rd.reader.pos] == request.message[..rd.reader.pos];
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..rd.reader.pos]);
      }
    }

    var decMatRequest := Materials.DecryptionMaterialsRequest(header.body.algorithmSuiteID, header.body.encryptedDataKeys.entries, header.body.aad);
    var decMat :- cmm.DecryptMaterials(decMatRequest);

    var decryptionKey := DeriveKey(decMat.plaintextDataKey.get, decMat.algorithmSuiteID, header.body.messageID);

    ghost var endHeaderPos := rd.reader.pos;
    // Parse and decrypt the message body
    var plaintext;
    match header.body.contentType {
      case NonFramed =>
        plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.messageID);
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.frameLength as int, header.body.messageID);
    }
    assert header.body.contentType.Framed? ==> (
      exists frames: seq<MessageBody.Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid()) 
        && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos..rd.reader.pos] :: 
          && MessageBody.FramesEncryptPlaintext(frames, plaintext));
    ghost var frames: seq<MessageBody.Frame> :| header.body.contentType.Framed? ==> 
        (|frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid()) 
        && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos..rd.reader.pos] 
        && MessageBody.FramesEncryptPlaintext(frames, plaintext));
        
    assert header.body.contentType.Framed? ==> FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]) by {
      reveal FramesBySequence();
      assert header.body.contentType.Framed? ==> |frames| < UINT32_LIMIT;
      assert header.body.contentType.Framed? ==> forall frame | frame in frames :: frame.Valid();
      assert header.body.contentType.Framed? ==> rd.reader.data[endHeaderPos..rd.reader.pos] == MessageBody.FramesToSequence(frames);
    }

    assert header.body.contentType.Framed? ==> HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]) 
      && FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]) by {
        assert header.body.contentType.Framed? ==>  endHeaderPos == |deserializeHeaderResult.hbSeq| + |header.auth.iv + header.auth.authenticationTag|;
        assert header.body.contentType.Framed? ==> HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]);
        assert header.body.contentType.Framed? ==> FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]);
      }

    ghost var signature;
    ghost var endFramePos := rd.reader.pos;
    assert header.body.contentType.Framed? ==> 0 <= endHeaderPos <= endFramePos <= |request.message|;
    if decMat.algorithmSuiteID.SignatureType().Some? {
      var verifyResult, locSig := VerifySignature(rd, decMat);
      signature := locSig;
      if verifyResult.Failure? {
        return Failure(verifyResult.error);
      }
      assert SignatureBySequence(signature, rd.reader.data[endFramePos..rd.reader.pos]);
    }
    
    var isDone := rd.IsDoneReading();
    if !isDone {
      return Failure("message contains additional bytes at end");
    }

    // Combine gathered facts and convert to postcondition
    if header.body.contentType.Framed? { 
      if decMat.algorithmSuiteID.SignatureType().Some? { // Case with Signature
        assert SignatureBySequence(signature, rd.reader.data[endFramePos..rd.reader.pos]); 
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos])
          && FramesBySequence(frames, request.message[endHeaderPos..endFramePos])
          && SignatureBySequence(signature, request.message[endFramePos..]) by {
            assert 0 <= endHeaderPos <= endFramePos <= |request.message|;
            assert SignatureBySequence(signature, request.message[endFramePos..]) by {
            assert header.body.contentType.Framed? ==> SignatureBySequence(signature, rd.reader.data[endFramePos..rd.reader.pos]);
            assert rd.reader.data[endFramePos..rd.reader.pos] == request.message[endFramePos..] by {
              calc {
                rd.reader.data[endFramePos..rd.reader.pos];
              == {upperBoundRemv(rd.reader.data, endFramePos); }
                rd.reader.data[endFramePos..];
              == {assert rd.reader.data == request.message; }
                request.message[endFramePos..];
              }
            }
            assert SignatureBySequence(signature, rd.reader.data[endFramePos..rd.reader.pos]);
          }
        }
        HBandMBwithSigMatchSequence(header, deserializeHeaderResult.hbSeq, frames, signature, request.message);
      } else { // Case without signature  
        assert 0 <= endHeaderPos <= |request.message| by {
          assert request.message == rd.reader.data;
        }
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos])
          && FramesBySequence(frames, request.message[endHeaderPos..]) by {
            assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]) 
              && FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]);
            assert rd.reader.data[endHeaderPos..rd.reader.pos] == request.message[endHeaderPos..] by {
              calc {
                rd.reader.data[endHeaderPos..rd.reader.pos];
              == {upperBoundRemv(rd.reader.data, endHeaderPos); }
                rd.reader.data[endHeaderPos..];
              == {assert rd.reader.data == request.message; }
                request.message[endHeaderPos..];
              }
            }
          }
        assert 0 <= endHeaderPos <= |request.message|; 
        HBandMBMatchSequence(header, deserializeHeaderResult.hbSeq, frames, request.message);
      }
    }
    var decryptResultWithVerificationInfo := DecryptResultWithVerificationInfo(plaintext, header, deserializeHeaderResult.hbSeq, frames, signature);
    return Success(decryptResultWithVerificationInfo);
  }

  method VerifySignature(rd: Streams.ByteReader, decMat: Materials.ValidDecryptionMaterials) returns (res: Result<bool>, ghost signature: seq<uint8>) 
    requires rd.Valid()
    requires decMat.algorithmSuiteID.SignatureType().Some?
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res
      case Failure(_) => true
      case Success(b) =>
        && b
        && 2 <= old(rd.reader.pos) + 2 <= rd.reader.pos
        && SignatureBySequence(signature, rd.reader.data[old(rd.reader.pos)..rd.reader.pos])
  {
    var ecdsaParams := decMat.algorithmSuiteID.SignatureType().get;
    var usedCapacity := rd.GetSizeRead();
    assert usedCapacity == rd.reader.pos;
    var msg := rd.reader.data[..usedCapacity];  // unauthenticatedHeader + authTag + body
    // read signature
    var signatureLengthResult := rd.ReadUInt16();
    if signatureLengthResult.Failure? {
      return Failure(signatureLengthResult.error), [];
    }
    var sigResult := rd.ReadBytes(signatureLengthResult.value as nat);
    if sigResult.Failure? {
      return Failure(sigResult.error), [];
    }
    // verify signature
    var signatureVerifiedResult := Signature.Verify(ecdsaParams, decMat.verificationKey.get, msg, sigResult.value);
    if signatureVerifiedResult.Failure? {
      return signatureVerifiedResult, [];
    }
    if !signatureVerifiedResult.value {
      return Failure("signature not verified"), [];
    }
    
    assert SignatureBySequence(sigResult.value, rd.reader.data[old(rd.reader.pos)..rd.reader.pos]) by {
      reveal SignatureBySequence(); 
    }
    return Success(true), sigResult.value;
  }

  predicate {:opaque } HeaderBySequence(header: Msg.Header, hbSeq: seq<uint8>, sequence: seq<uint8>)
  {
    header.body.contentType.Framed?
    && header.body.Valid()
    && Msg.SeqToHeaderBody(hbSeq, header.body)
    && sequence == hbSeq + header.auth.iv + header.auth.authenticationTag
  }

  predicate {:opaque } FramesBySequence(frames: seq<MessageBody.Frame>, sequence: seq<uint8>)
  {
    |frames| < UINT32_LIMIT
    && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid())
    && sequence == MessageBody.FramesToSequence(frames)
  }

  predicate {:opaque } SignatureBySequence(signature: seq<uint8>, sequence: seq<uint8>)
  {
    |signature| < UINT16_LIMIT
    && sequence == UInt16ToSeq(|signature| as uint16) + signature
  }

  lemma HBandMBMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag|
    requires exists headerLength | 0 <= headerLength <= |message| ::
      HeaderBySequence(header, hbSeq, message[..headerLength])
      && FramesBySequence(frames, message[headerLength..])
    ensures message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames);
  {
    reveal HeaderBySequence(), FramesBySequence();
  }

  lemma HBandMBwithSigMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, signature: seq<uint8>, message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag| + |MessageBody.FramesToSequence(frames)|
    requires exists headerLength, frameLength | 0 <= headerLength <= frameLength < |message| ::
      HeaderBySequence(header, hbSeq, message[..headerLength])
      && FramesBySequence(frames, message[headerLength..frameLength])
      && SignatureBySequence(signature, message[frameLength..])
    ensures |signature| < UINT16_LIMIT &&
      message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames) + UInt16ToSeq(|signature| as uint16) + signature;
  {
    reveal HeaderBySequence(), FramesBySequence(), SignatureBySequence();
  }

  lemma concatSeq(sequence: seq<uint8>, i: nat)
    requires 0 <= i <= |sequence|
    ensures sequence[..i] + sequence[i..] == sequence
  {

  }

  lemma upperBoundRemv(sequence: seq<uint8>, lo: int)
    requires 0 <= lo <= |sequence|
    ensures sequence[lo..|sequence|] == sequence[lo..]
  {

  }

  predicate DataIsFramed(sequence: seq<uint8>)
  {
    exists i, header, hbSeq | 0 <= i <= |sequence| :: HeaderBySequence(header, hbSeq, sequence[..i])
  }

}
