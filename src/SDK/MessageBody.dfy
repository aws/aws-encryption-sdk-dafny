// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Serialize/SerializableTypes.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Util/Streams.dfy"
include "../Util/UTF8.dfy"
include "Serialize/Frames.dfy"

include "Serialize/Header.dfy"
include "Serialize/HeaderTypes.dfy"
include "Serialize/V1HeaderBody.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/SerializeFunctions.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"

module MessageBody {
  // export
  //   provides EncryptMessageBody, DecryptFramedMessageBody, DecryptNonFramedMessageBody,
  //     Wrappers, UInt, Streams, Client,
  //     FramesEncryptPlaintext, AESEncryption, DecryptedWithKey
  //   reveals  SeqWithGhostFrames

  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import Streams
  import UTF8
  import SerializableTypes
  import MaterialProviders.Client
  import Frames
  import Header
  import opened SerializeFunctions
  import Seq
  import StandardLibrary

  datatype BodyAADContent = AADRegularFrame | AADFinalFrame | AADSingleBlock

  const BODY_AAD_CONTENT_REGULAR_FRAME: string := "AWSKMSEncryptionClient Frame"
  const BODY_AAD_CONTENT_FINAL_FRAME: string := "AWSKMSEncryptionClient Final Frame"
  const BODY_AAD_CONTENT_SINGLE_BLOCK: string := "AWSKMSEncryptionClient Single Block"

  function method BodyAADContentTypeString(bc: BodyAADContent): string {
    match bc
    case AADRegularFrame => BODY_AAD_CONTENT_REGULAR_FRAME
    case AADFinalFrame => BODY_AAD_CONTENT_FINAL_FRAME
    case AADSingleBlock => BODY_AAD_CONTENT_SINGLE_BLOCK
  }

  const START_SEQUENCE_NUMBER: uint32 := Frames.START_SEQUENCE_NUMBER
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := Frames.ENDFRAME_SEQUENCE_NUMBER
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := Frames.NONFRAMED_SEQUENCE_NUMBER

  function method IVSeq(suite: Client.AlgorithmSuites.AlgorithmSuite, sequenceNumber: uint32)
    :(ret: seq<uint8>)
    //= compliance/data-format/message-body.txt#2.5.2.1.2
    //= type=implication
    //# The IV length MUST be equal to the IV
    //# length of the algorithm suite specified by the Algorithm Suite ID
    //# (message-header.md#algorithm-suite-id) field.
    //
    //= compliance/data-format/message-body.txt#2.5.2.2.3
    //= type=implication
    //# The IV length MUST be equal to the IV length of the algorithm suite
    //# (../framework/algorithm-suites.md) that generated the message.
    ensures |ret| == suite.encrypt.ivLength as nat
  {
    seq(suite.encrypt.ivLength as int - 4, _ => 0) + UInt32ToSeq(sequenceNumber)
  }

  //= compliance/data-format/message-body.txt#2.5.2.1.2
  //= type=implication
  //# Each frame in the Framed Data (Section 2.5.2) MUST include an IV that
  //# is unique within the message.
  //
  //= compliance/data-format/message-body.txt#2.5.2.2.3
  //= type=implication
  //# The IV MUST be a unique IV within the message.
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

  /**
    Predicate states that frames encrypt plaintext

      Plaintext is split into chunks of frameLength. One chunck is encrypted in one frame. Reasoning about chunks makes proving predicate easier
        FramesEncryptPlaintextSegments: States that sequence of frames decrypts to sequence of chunks
        SumPlaintextSegments: States that sum of chunks is the plaintext
   */
  predicate FramesEncryptPlaintext(frames: FramedMessage, plaintext: seq<uint8>)
  {
    exists plaintextSeg: seq<seq<uint8>>
    ::
      && FramesEncryptPlaintextSegments(frames.regularFrames + [frames.finalFrame], plaintextSeg)
      && SumPlaintextSegments(plaintextSeg) == plaintext
  }

  predicate FramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>)
  {
    // The total number of frames MUST equal the total number of plaintext segments.
    if |frames| != |plaintextSeg| then
      false
    else
    // No more regular frames, check the tail
    if frames == [] then
      true
    else
      // Drop the segments
      && FramesEncryptPlaintextSegments(Seq.DropLast(frames), Seq.DropLast(plaintextSeg))
      && AESEncryption.CiphertextGeneratedWithPlaintext(Seq.Last(frames).encContent, Seq.Last(plaintextSeg))
  }

  function SumPlaintextSegments(plaintextSeg: seq<seq<uint8>>): seq<uint8>
  {
    if plaintextSeg == [] then
      []
    else
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg| - 1]) + plaintextSeg[|plaintextSeg| - 1]
  }

  type MessageRegularFrames = regularFrames: seq<Frames.RegularFrame>
    | IsMessageRegularFrames(regularFrames)
    witness *

  predicate MessageFramesAreMonotonic(frames: seq<MessageFrame>){
    if |frames| == 0 then true
    else
      // Cardinality can be thought of as the tail index
      // of a one-based indexed array.
      // Sequence number is the one-based indexed array of frames
      && |frames| == Seq.Last(frames).seqNum as nat
      && MessageFramesAreMonotonic(Seq.DropLast(frames))
  }

  predicate MessageFramesAreForTheSameMessage(frames: seq<MessageFrame>){
    forall i
      // This excludes the First frame in the seq
      // because all headers are definitionally equal for `[]` and `[frame]`.
      | 0 < i < |frames|
    ::  Seq.First(frames).header == frames[i].header
  }

  predicate IsMessageRegularFrames(regularFrames: seq<Frames.RegularFrame>) {
    // The total number of frames MUST be at most UINT32_MAX.
    // And a RegularFrame can not have a sequence number
    // equal to the ENDFRAME_SEQUENCE_NUMBER.
    //
    //= compliance/data-format/message-body.txt#2.5.2
    //= type=implication
    //# *  The number of frames in a single message MUST be less than or
    //# equal to "2^32 - 1".
    && 0 <= |regularFrames| < ENDFRAME_SEQUENCE_NUMBER as nat
       // The sequence number MUST be monotonic
       //
       //= compliance/data-format/message-body.txt#2.5.2.1.1
       //= type=implication
       //# Framed Data MUST start at Sequence Number 1.
       //
       //= compliance/data-format/message-body.txt#2.5.2.1.1
       //= type=implication
       //# Subsequent frames MUST be in order and MUST contain an increment of 1
       //# from the previous frame.
    && MessageFramesAreMonotonic(regularFrames)
       // All frames MUST all be from the same messages i.e. the same header
    && MessageFramesAreForTheSameMessage(regularFrames)
  }

  type NonFramedMessage = Frames.NonFramed

  datatype FramedMessageBody = FramedMessageBody(
    regularFrames: MessageRegularFrames,
    //= compliance/data-format/message-body.txt#2.5.2.2
    //= type=implication
    //# Framed data MUST contain exactly one final frame.
    finalFrame: Frames.FinalFrame
  )

  type FramedMessage = body: FramedMessageBody
    |
      //= compliance/data-format/message-body.txt#2.5.2.2.2
      //= type=implication
      //# The Final Frame Sequence number MUST be equal to the total number of
      //# frames in the Framed Data.
      && MessageFramesAreMonotonic(body.regularFrames + [body.finalFrame])
      && MessageFramesAreForTheSameMessage(body.regularFrames + [body.finalFrame])
    witness *

  type MessageFrame = frame: Frames.Frame
    |
      || Frames.IsFinalFrame(frame)
      || Frames.IsRegularFrame(frame)
    witness *

  type Frame = frame: Frames.Frame
    |
      || Frames.IsFinalFrame(frame)
      || Frames.IsRegularFrame(frame)
      || Frames.IsNonFramed(frame)
    witness *

  lemma LemmaAddingNextRegularFrame(
    regularFrames: MessageRegularFrames,
    nextRegularFrame: Frames.RegularFrame
  )
    requires |regularFrames| + 1 < ENDFRAME_SEQUENCE_NUMBER as nat
    requires nextRegularFrame.seqNum as nat == |regularFrames| + 1 as nat
    requires MessageFramesAreForTheSameMessage(regularFrames + [nextRegularFrame])
    ensures IsMessageRegularFrames(regularFrames + [nextRegularFrame])
  {}

  method EncryptMessageBody(
    plaintext: seq<uint8>,
    header : Header.Header,
    key: seq<uint8>
  )
    returns (result: Result<FramedMessage, string>)
    requires |key| ==  header.suite.encrypt.keyLength as nat
    requires 0 < header.body.frameLength as nat < UINT32_LIMIT
    requires header.body.contentType.Framed?
    ensures match result
            case Failure(e) => true
            case Success(body) =>
              && (forall frame: Frames.Frame
                    | frame in body.regularFrames
                  :: AESEncryption.EncryptedWithKey(frame.encContent, key))
              && AESEncryption.EncryptedWithKey(body.finalFrame.encContent, key)
  {
    var n : int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    var regularFrames: MessageRegularFrames := [];

    //= compliance/client-apis/encrypt.txt#2.7
    //# Before the end of the input is indicated, this operation MUST process
    //# as much of the consumable bytes as possible by constructing regular
    //# frames (Section 2.7.1).

    //= compliance/client-apis/encrypt.txt#2.7
    //# If an end to the input has been indicated, there are no more
    //# consumable plaintext bytes to process, and a final frame has not yet
    //# been constructed, this operation MUST construct an empty final frame
    //# (Section 2.7.1).
    // This one is true because of our while loop construction below, where we check that
    // adding another frame puts us at < |plaintext|. This means we will never
    // consume the entire plaintext in this while loop, and will always construct
    // a final frame after exiting it.
    while n + header.body.frameLength as nat < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant |regularFrames| == (sequenceNumber - START_SEQUENCE_NUMBER) as nat
      invariant forall frame: Frames.Frame
                  | frame in regularFrames
                ::
                  && AESEncryption.EncryptedWithKey(frame.encContent, key)
                  && frame.header == header
    {
      :- Need(sequenceNumber < ENDFRAME_SEQUENCE_NUMBER, "too many frames");
      var plaintextFrame := plaintext[n..n + header.body.frameLength as nat];

      //= compliance/client-apis/encrypt.txt#2.7
      //# *  If there are enough input plaintext bytes consumable to create a
      //# new regular frame, such that creating a regular frame does not
      //# processes all consumable bytes, then this operation MUST construct
      //# a regular frame (Section 2.7.1) using the consumable plaintext
      //# bytes.
      var regularFrame :- EncryptRegularFrame(
        key,
        header,
        plaintextFrame,
        sequenceNumber
      );

      assert regularFrame.seqNum as nat == |regularFrames| + 1;
      LemmaAddingNextRegularFrame(regularFrames, regularFrame);

      regularFrames := regularFrames + [regularFrame];

      n := n + header.body.frameLength as nat;

      //= compliance/client-apis/encrypt.txt#2.7.1
      //# Otherwise, this value MUST be 1 greater than
      //# the value of the sequence number of the previous frame.
      sequenceNumber := sequenceNumber + 1;
    }

    //= compliance/client-apis/encrypt.txt#2.7
    //# *  If there are not enough input consumable plaintext bytes to create
    //# a new regular frame, then this operation MUST construct a final
    //# frame (Section 2.7.1)
    //
    //= compliance/data-format/message-body.txt#2.5.2.2
    //# *  When the length of the Plaintext is less than the Frame Length,
    //# the body MUST contain exactly one frame and that frame MUST be a
    //# Final Frame.

    //= compliance/client-apis/encrypt.txt#2.7
    //# *  If there are exactly enough consumable plaintext bytes to create
    //# one regular frame, such that creating a regular frame processes
    //# all consumable bytes, then this operation MUST construct either a
    //# final frame or regular frame (Section 2.7.1) with the remaining
    //# plaintext.
    //
    //= compliance/data-format/message-body.txt#2.5.2.2
    //# *  When the length of the Plaintext is an exact multiple of the Frame
    //# Length (including if it is equal to the frame length), the Final
    //# Frame encrypted content length SHOULD be equal to the frame length
    //# but MAY be 0.
    var finalFrame :- EncryptFinalFrame(
      key,
      header,
      plaintext[n..],
      sequenceNumber
    );

    assert MessageFramesAreForTheSameMessage(regularFrames + [finalFrame]);

    return Success(FramedMessageBody(
                     regularFrames := regularFrames,
                     finalFrame := finalFrame
                   ));
  }

  method EncryptRegularFrame(
    key: seq<uint8>,
    header: Header.Header,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<Frames.RegularFrame, string>)
    requires |key| == header.suite.encrypt.keyLength as int
    requires 0 < header.body.frameLength as nat < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber < ENDFRAME_SEQUENCE_NUMBER
    requires header.body.contentType.Framed?
    requires |plaintext| < UINT32_LIMIT

    //= compliance/client-apis/encrypt.txt#2.7.1
    //= type=implication
    //# -  For a regular frame the length of this plaintext subsequence
    //# MUST equal the frame length.
    requires |plaintext| == header.body.frameLength as nat && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    ensures match res
            case Failure(e) => true
            case Success(frame) =>
              && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
              && AESEncryption.EncryptedWithKey(frame.encContent, key)
              && frame.seqNum == sequenceNumber
              && frame.header == header
  {
    //= compliance/client-apis/encrypt.txt#2.7.1
    //# To construct a regular or final frame that represents the next frame
    //# in the encrypted message's body, this operation MUST calculate the
    //# encrypted content and an authentication tag using the authenticated
    //# encryption algorithm (../framework/algorithm-suites.md#encryption-
    //# algorithm) specified by the algorithm suite (../framework/algorithm-
    //# suites.md), with the following inputs:
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := IVSeq(header.suite, sequenceNumber);

    // *  The AAD is the serialized message body AAD (../data-format/
    //    message-body-aad.md), constructed as follows:
    var aad := BodyAAD(
      // -  The message ID (../data-format/message-body-aad.md#message-id)
      //    is the same as the message ID (../data-frame/message-
      //    header.md#message-id) serialized in the header of this message.
      header.body.messageId,
      AADRegularFrame,
      sequenceNumber,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# -  The content length (../data-format/message-body-aad.md#content-
      //# length) MUST have a value equal to the length of the plaintext
      //# being encrypted.
      |plaintext| as uint64
    );

    var encryptionOutput :- AESEncryption.AESEncrypt(
      header.suite.encrypt,
      iv,
      key,
      plaintext,
      aad
    );

    //= compliance/client-apis/encrypt.txt#2.7.1
    //# This operation MUST serialize a regular frame or final frame with the
    //# following specifics:
    var frame: Frames.RegularFrame := Frames.Frame.RegularFrame(
      header,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# *  Sequence Number (../data-format/message-body.md#sequence-number):
      //# MUST be the sequence number of this frame, as determined above.
      sequenceNumber,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# *  IV (../data-format/message-body.md#iv): MUST be the IV used when
      //# calculating the encrypted content above
      iv,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# *  Encrypted Content (../data-format/message-body.md#encrypted-
      //# content): MUST be the encrypted content calculated above.
      encryptionOutput.cipherText,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# *  Authentication Tag (../data-format/message-body.md#authentication-
      //# tag): MUST be the authentication tag output when calculating the
      //# encrypted content above.
      encryptionOutput.authTag
    );

    return Success(frame);
  }

  method EncryptFinalFrame(
    key: seq<uint8>,
    header: Header.Header,
    plaintext: seq<uint8>,
    sequenceNumber: uint32
  )
    returns (res: Result<Frames.FinalFrame, string>)
    requires |key| == header.suite.encrypt.keyLength as nat
    requires START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires 0 <= |plaintext| < UINT32_LIMIT
    requires header.body.contentType.Framed?
    //= compliance/client-apis/encrypt.txt#2.7.1
    //= type=implication
    //# -  For a final frame this MUST be the remaining plaintext bytes
    //# which have not yet been encrypted, whose length MUST be equal
    //# to or less than the frame length.
    //
    //= compliance/data-format/message-body.txt#2.5.2.2
    //= type=implication
    //# The length of the plaintext to be encrypted in the Final Frame MUST
    //# be greater than or equal to 0 and less than or equal to the Frame
    //# Length (message-header.md#frame-length).
    requires |plaintext| <= header.body.frameLength as nat
    ensures match res
            case Failure(e) => true
            case Success(frame) =>
              && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext)
              && AESEncryption.EncryptedWithKey(frame.encContent, key)
              && frame.seqNum == sequenceNumber
              && frame.header == header
  {

    var iv := IVSeq(header.suite, sequenceNumber);

    var aad := BodyAAD(
      header.body.messageId,
      AADFinalFrame,
      sequenceNumber,
      //= compliance/client-apis/encrypt.txt#2.7.1
      //# o  For a final frame this MUST be the length of the remaining
      //# plaintext bytes which have not yet been encrypted, whose
      //# length MUST be equal to or less than the frame length.
      |plaintext| as uint64
    );

    var encryptionOutput :- AESEncryption.AESEncrypt(
      header.suite.encrypt,
      iv,
      key,
      plaintext,
      aad
    );

    var finalFrame: Frames.FinalFrame := Frames.Frame.FinalFrame(
      header,
      sequenceNumber,
      iv,
      encryptionOutput.cipherText,
      encryptionOutput.authTag
    );

    return Success(finalFrame);
  }

  method DecryptFramedMessageBody(
    body: FramedMessage,
    key: seq<uint8>
  )
    returns (res: Result<seq<uint8>, string>)
    requires |key| == body.finalFrame.header.suite.encrypt.keyLength as int
    ensures match res
            case Failure(_) => true
            case Success(plaintext) => //Exists a sequence of frames which encrypts the plaintext and is serialized in the read section of the stream
              && FramesEncryptPlaintext(body, plaintext)
              && DecryptedWithKey(key, plaintext)
  {
    var plaintext := [];
    // var n: uint32 := 1;
    ghost var decryptedFrames: seq<Frames.RegularFrame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := []; // Chunks of plaintext which are decrypted from the frame

    for i := 0 to |body.regularFrames|
      invariant body.regularFrames[..i] == decryptedFrames
      // The goal is to assert FramesEncryptPlaintext.
      // But this requires the final frame e.g. a FramedMessage.
      // So I decompose this predicate into its parts
      invariant FramesEncryptPlaintextSegments(decryptedFrames, plaintextSeg) // So far: All decrypted frames decrypt to the list of plaintext chunks
      invariant SumPlaintextSegments(plaintextSeg) == plaintext // So far: The current plaintext is the sum of all decrypted chunks
      invariant DecryptedSegmentsWithKey(key, plaintextSeg)
      invariant DecryptedWithKey(key, plaintext)
    {

      var plaintextSegment :- DecryptFrame(body.regularFrames[i], key);

      plaintext := plaintext + plaintextSegment;
      plaintextSeg := plaintextSeg + [plaintextSegment];
      decryptedFrames := decryptedFrames + [body.regularFrames[i]];

      StandardLibrary.SeqTakeAppend(body.regularFrames, i);
    }
    var finalPlaintextSegment :- DecryptFrame(body.finalFrame, key);
    plaintext := plaintext + finalPlaintextSegment;
    plaintextSeg := plaintextSeg + [finalPlaintextSegment];

    assert FramesEncryptPlaintextSegments([body.finalFrame], [finalPlaintextSegment]);
    assert body.regularFrames == decryptedFrames;
    assert FramesEncryptPlaintextSegments(body.regularFrames + [body.finalFrame], plaintextSeg);
    assert SumPlaintextSegments(plaintextSeg) == plaintext;

    return Success(plaintext);
  }

  method DecryptFrame(
    frame: Frame,
    key: seq<uint8>
  )
    returns (res: Result<seq<uint8>, string>)
    requires |key| == frame.header.suite.encrypt.keyLength as int
    ensures match res
            case Success(plaintextSegment) => ( // Decrypting the frame encoded in the stream is the returned ghost frame
              && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextSegment)
              && AESEncryption.DecryptedWithKey(key, plaintextSegment)
              && (frame.RegularFrame? || frame.FinalFrame? ==> |plaintextSegment| < UINT32_LIMIT)
            )
            case Failure(_) => true
  {
    var aad := BodyAADByFrameType(frame);

    //= compliance/client-apis/decrypt.txt#2.7.4
    //# If this decryption fails, this operation MUST immediately halt and
    //# fail.
    var plaintextSegment :-
      // This is here as a citation for the decryption.
      // The manner in which it is currently called does not allow for a
      // single frame to be decrypted. We are ok with this as there is no
      // streaming.
      //= compliance/client-apis/decrypt.txt#2.7.4
      //= type=exception
      //# Once at least a single frame is deserialized (or the entire body in
      //# the un-framed case), this operation MUST decrypt and authenticate the
      //# frame (or body) using the authenticated encryption algorithm
      //# (../framework/algorithm-suites.md#encryption-algorithm) specified by
      //# the algorithm suite (../framework/algorithm-suites.md), with the
      //# following inputs:
      AESEncryption.AESDecrypt(
        frame.header.suite.encrypt,
        //#*  The cipherkey is the derived data key
        key,
        //#*  The ciphertext is the encrypted content (../data-format/message-
        //#   body.md#encrypted-content).
        frame.encContent,
        //#*  the tag is the value serialized in the authentication tag field
        //#   (../data-format/message-body.md#authentication-tag) in the message
        //#   body or frame.
        frame.authTag,
        //#*  The IV is the sequence number (../data-format/message-body-
        //#   aad.md#sequence-number) used in the message body AAD above, padded
        //#   to the IV length (../data-format/message-header.md#iv-length) with
        //#   0.
        frame.iv,
        //#*  The AAD is the serialized message body AAD (../data-format/
        //#   message-body-aad.md)
        aad
      );

    return Success(plaintextSegment);
  }

  /*
   * Extracts the Body Additional Authenticated Data as per the
   * AWS Encryption SDK Spececification for Message Body AAD.
   */
  method BodyAADByFrameType(
    frame: Frame
  )
    returns (aad: seq<uint8>)
  {
    var (sequenceNumber, bc, length) := match frame
      case RegularFrame(header,seqNum,_,_,_) => (
      //= compliance/data-format/message-body-aad.txt#2.4.3
      //# For framed data (message-body.md#framed-data), the value of this
      //# field MUST be the frame sequence number (message-body.md#sequence-
      //# number).
      seqNum,

      //= compliance/data-format/message-body-aad.txt#2.4.2
      //# *  The regular frames (message-body.md#regular-frame) in framed data
      //# (message-body.md#framed-data) MUST use the value
      //# "AWSKMSEncryptionClient Frame".
      AADRegularFrame,

      //= compliance/data-format/message-body-aad.txt#2.4.4
      //# *  For framed data (message-body.md#framed-data), this value MUST
      //# equal the length, in bytes, of the plaintext being encrypted in
      //# this frame.

      //= compliance/data-format/message-body-aad.txt#2.4.4
      //# -  For regular frames (message-body.md#regular-frame), this value
      //# MUST equal the value of the frame length (message-
      //# header.md#frame-length) field in the message header.
      header.body.frameLength as uint64
      )
      case FinalFrame(_,seqNum,_, encContent,_) => (
      //= compliance/data-format/message-body-aad.txt#2.4.3
      //# For framed data (message-body.md#framed-data), the value of this
      //# field MUST be the frame sequence number (message-body.md#sequence-
      //# number).
      seqNum,

      //= compliance/data-format/message-body-aad.txt#2.4.2
      //# *  The final frame (message-body.md#final-frame) in framed data
      //# (message-body.md#framed-data) MUST use the value
      //# "AWSKMSEncryptionClient Final Frame".
      AADFinalFrame,

      //= compliance/data-format/message-body-aad.txt#2.4.4
      //# *  For framed data (message-body.md#framed-data), this value MUST
      //# equal the length, in bytes, of the plaintext being encrypted in
      //# this frame.

      //= compliance/data-format/message-body-aad.txt#2.4.4
      //# -  For the final frame (message-body.md#final-frame), this value
      //# MUST be greater than or equal to 0 and less than or equal to
      //# the value of the frame length (message-header.md#frame-length)
      //# field in the message header.
      |encContent| as uint64
      )
      case NonFramed(_,_,encContent,_) => (
      //= compliance/client-apis/decrypt.txt#2.7.4
      //# If this is un-framed data,
      //# this value MUST be 1.

      //= compliance/data-format/message-body-aad.txt#2.4.3
      //# For non-framed data (message-body.md#non-framed-data), the
      //# value of this field MUST be "1".
      NONFRAMED_SEQUENCE_NUMBER,

      //= compliance/data-format/message-body-aad.txt#2.4.2
      //# *  Non-framed data (message-body.md#non-framed-data) MUST use the
      //# value "AWSKMSEncryptionClient Single Block".
      AADSingleBlock,

      //= compliance/data-format/message-body-aad.txt#2.4.4
      //# *  For non-framed data (message-body.md#non-framed-data), this value
      //# MUST equal the length, in bytes, of the plaintext data provided to
      //# the algorithm for encryption.
      |encContent| as uint64
      );

    aad := BodyAAD(frame.header.body.messageId, bc, sequenceNumber, length);
  }

  /*
   * Serializes the Message Body ADD
   */
  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64) returns (aad: seq<uint8>) {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    //= compliance/client-apis/decrypt.txt#2.7.4
    //#*  The AAD is the serialized message body AAD (../data-format/
    //#   message-body-aad.md), constructed as follows:
    aad :=
      //# -  The message ID (../data-format/message-body-aad.md#message-id)
      //#    is the same as the message ID (../data-frame/message-
      //#    header.md#message-id) deserialized from the header of this
      //#    message.
      messageID
      //# -  The Body AAD Content (../data-format/message-body-aad.md#body-
      //#    aad-content) depends on whether the thing being decrypted is a
      //#    regular frame, final frame, or un-framed data.  Refer to
      //#    Message Body AAD (../data-format/message-body-aad.md)
      //#    specification for more information.
      + contentAAD.value
      //# -  The sequence number (../data-format/message-body-
      //#    aad.md#sequence-number) is the sequence number deserialized
      //#    from the frame being decrypted.
      + UInt32ToSeq(sequenceNumber)
      //= compliance/client-apis/decrypt.txt#2.7.4
      //# -  The content length (../data-format/message-body-aad.md#content-
      //# length) MUST have a value equal to the length of the plaintext
      //# that was encrypted.
      + UInt64ToSeq(length)
      ;
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

  function method WriteFramedMessageBody(
    body: FramedMessage
  )
    :(ret: seq<uint8>)
    //= compliance/data-format/message-body.txt#2.5.2.2
    //= type=implication
    //# The final frame
    //# MUST be the last frame.
    ensures ret == WriteMessageRegularFrames(body.regularFrames)
                   + Frames.WriteFinalFrame(body.finalFrame)
  {
    WriteMessageRegularFrames(body.regularFrames) + Frames.WriteFinalFrame(body.finalFrame)
  }

  function method WriteMessageRegularFrames(
    frames: MessageRegularFrames
  )
    :(ret: seq<uint8>)
    ensures if |frames| == 0 then
              ret == []
            else
              ret == WriteMessageRegularFrames(Seq.DropLast(frames))
              + Frames.WriteRegularFrame(Seq.Last(frames))
  {
    if |frames| == 0 then []
    else
      WriteMessageRegularFrames(Seq.DropLast(frames))
      + Frames.WriteRegularFrame(Seq.Last(frames))
  }

  function method ReadFramedMessageBody(
    buffer: ReadableBuffer,
    header: Frames.FramedHeader,
    regularFrames: MessageRegularFrames,
    continuation: ReadableBuffer
  )
    :(res: ReadCorrect<FramedMessage>)
    requires forall frame: Frames.Frame
               | frame in regularFrames
             :: frame.header == header
    requires CorrectlyReadRange(buffer, continuation)
    requires CorrectlyRead(buffer, Success(SuccessfulRead(regularFrames, continuation)), WriteMessageRegularFrames)
    decreases ENDFRAME_SEQUENCE_NUMBER as nat - |regularFrames|
    ensures CorrectlyRead(buffer, res, WriteFramedMessageBody)
    ensures res.Success?
            ==>
              && res.value.data.finalFrame.header == header
  {
    var sequenceNumber :- ReadUInt32(continuation);

    //= compliance/client-apis/decrypt.txt#2.7.4
    //# If deserializing framed data (../data-format/message-body.md#framed-
    //# data), this operation MUST use the first 4 bytes of a frame to
    //# determine if the frame MUST be deserialized as a final frame
    //# (../data-format/message-body.md#final-frame) or regular frame
    //# (../fata-format/message-body/md#regular-frame).
    if (sequenceNumber.data != ENDFRAME_SEQUENCE_NUMBER) then

      assert {:split_here} true;

      //= compliance/client-apis/decrypt.txt#2.7.4
      //# Otherwise, this MUST
      //# be deserialized as the sequence number (../data-format/message-
      //# header.md#sequence-number) and the following bytes according to the
      //# regular frame spec (../data-format/message-body.md#regular-frame).
      var regularFrame :- Frames.ReadRegularFrame(continuation, header);
      //= compliance/client-apis/decrypt.txt#2.7.4
      //# If this is framed data and the first
      //# frame sequentially, this value MUST be 1.
      // Where this is the seqNum
      // Imagine that |regularFrames| is 0, than seqNum is 1
      //= compliance/client-apis/decrypt.txt#2.7.4
      //# Otherwise, this
      //# value MUST be 1 greater than the value of the sequence number
      //# of the previous frame.
      :- Need(regularFrame.data.seqNum as nat == |regularFrames| + 1, Error("Sequence number out of order."));

      assert {:split_here} true;
      LemmaAddingNextRegularFrame(regularFrames, regularFrame.data);

      var nextRegularFrames: MessageRegularFrames := regularFrames + [regularFrame.data];

      assert {:split_here} true;
      assert CorrectlyRead(continuation, Success(regularFrame), Frames.WriteRegularFrame);
      ghost var why? := [buffer, continuation, regularFrame.tail];
      assert {:split_here} true;
      ConsecutiveReadsAreAssociative(why?);

      assert {:split_here} true;

      // This method recursively reads all the frames in the buffer,
      // instead of reading one frame a time, so this requirement cannot be met
      //= compliance/client-apis/decrypt.txt#2.7.4
      //= type=exception
      //# Once at least a single frame is deserialized (or the entire body in
      //# the un-framed case), this operation MUST decrypt and authenticate the
      //# frame (or body) using the authenticated encryption algorithm
      //# (../framework/algorithm-suites.md#encryption-algorithm) specified by
      //# the algorithm suite (../framework/algorithm-suites.md), with the
      //# following inputs:
      ReadFramedMessageBody(
        buffer,
        header,
        nextRegularFrames,
        regularFrame.tail
      )
    else
      //= compliance/client-apis/decrypt.txt#2.7.4
      //# If the first 4 bytes
      //# have a value of 0xFFFF, then this MUST be deserialized as the
      //# sequence number end (../data-format/message-header.md#sequence-
      //# number-end) and the following bytes according to the final frame spec
      //# (../data-format/message-body.md#final-frame).
      assert sequenceNumber.data == ENDFRAME_SEQUENCE_NUMBER;

      assert {:split_here} true;
      var finalFrame :- Frames.ReadFinalFrame(continuation, header);
      :- Need(
        finalFrame.data.seqNum as nat == |regularFrames| + 1,
        Error("Sequence number out of order.")
      );

      assert {:split_here} true;
      assert MessageFramesAreMonotonic(regularFrames + [finalFrame.data]);
      assert MessageFramesAreForTheSameMessage(regularFrames + [finalFrame.data]);

      var body: FramedMessage := FramedMessageBody(
        regularFrames := regularFrames,
        finalFrame := finalFrame.data
      );

      assert {:split_here} true;
      assert CorrectlyRead(continuation, Success(finalFrame), Frames.WriteFinalFrame);
      ghost var why? := [buffer, continuation, finalFrame.tail];
      assert {:split_here} true;
      ConsecutiveReadsAreAssociative(why?);

      assert {:split_here} true;
      Success(SuccessfulRead(body, finalFrame.tail))
  }

  function WriteNonFramedMessageBody(
    body: NonFramedMessage
  )
    :(ret: seq<uint8>)
    ensures ret == Frames.WriteNonFramed(body)
  {
    Frames.WriteNonFramed(body)
  }

  function method ReadNonFramedMessageBody(
    buffer: ReadableBuffer,
    header: Frames.NonFramedHeader
  )
    :(res: ReadCorrect<NonFramedMessage>)
    ensures CorrectlyRead(buffer, res, WriteNonFramedMessageBody)
    ensures res.Success?
            ==>
              && res.value.data.header == header
  {
    var block :- Frames.ReadNonFrame(buffer, header);
    Success(SuccessfulRead(block.data, block.tail))
  }
}
