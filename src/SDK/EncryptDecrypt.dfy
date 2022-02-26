// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "MessageBody.dfy"
include "../Crypto/Signature.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

include "Serialize/SerializableTypes.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/SerializeFunctions.dfy"


module {:extern "EncryptDecryptHelpers"} EncryptDecryptHelpers {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Aws.Crypto
  import MaterialProviders.Client
  import MessageBody
  import Signature
  import SerializableTypes
  import opened SerializeFunctions
  import HeaderAuth

    //= compliance/client-apis/encrypt.txt#2.4.6
    //= type=implication
    //# This
    //# value MUST default to 4096 bytes.
  const DEFAULT_FRAME_LENGTH : int64 := 4096

  // Specification of Encrypt with signature
  function method SerializeMessageWithSignature(
    framedMessage: MessageBody.FramedMessage,
    signature: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: Result<seq<uint8>, string>)
    requires |signature| < UINT16_LIMIT
    ensures res.Success?
    ==> 
      && var message := SerializeMessageWithoutSignature(framedMessage, suite);
      && message.Success?
      && res.value == message.value + WriteShortLengthSeq(signature)
  {
    var serializedSignature := WriteShortLengthSeq(signature);
    var serializedMessage :- SerializeMessageWithoutSignature(framedMessage, suite);
    Success(serializedMessage + serializedSignature)
  }

  // Specification of Encrypt without signature
  function method SerializeMessageWithoutSignature(
    framedMessage: MessageBody.FramedMessage,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(message: Result<seq<uint8>, string>)
  {
    // The header
    var headerAuth :- HeaderAuth.WriteHeaderAuthTag(framedMessage.finalFrame.header.headerAuth, suite);
    Success(
      //= compliance/client-apis/encrypt.txt#2.6.2
      //# The encrypted message output by this operation MUST have a message
      //# header equal to the message header calculated in this step.
      framedMessage.finalFrame.header.rawHeader
      // The header authentication
      + headerAuth
      // The message body i.e. "all the frames"
      + MessageBody.WriteFramedMessageBody(framedMessage)
    )
  }

  method VerifySignature(
    buffer: SerializeFunctions.ReadableBuffer,
    msg: seq<uint8>,
    decMat: Crypto.DecryptionMaterials
  )
    returns (res: Result<SerializeFunctions.ReadableBuffer, string>)
    // DecryptionMaterialsWithPlaintextDataKey ensures that the materials and the suite match.
    requires Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat)
    // TODO: Add Proof
    // ensures match res
    //   case Failure(_) => true
    //   case Success(_) =>
    //     && 2 <= old(rd.reader.pos) + 2 <= rd.reader.pos
    //     && SignatureBySequence(signature, rd.reader.data[old(rd.reader.pos)..rd.reader.pos])

    //= compliance/client-apis/decrypt.txt#2.7
    //= type=implication
    //# Otherwise this operation MUST NOT perform this
    //# step.
    ensures decMat.verificationKey.None? ==> res.Success? && res.value == buffer
    
  {
    // If there is no verification key, that lets us conclude that the suite does not have a signature.
    //= compliance/client-apis/decrypt.txt#2.7
    //# Otherwise this operation MUST NOT perform this
    //# step.
    if decMat.verificationKey.None? {
      return Success(buffer);
    }
    //= compliance/client-apis/decrypt.txt#2.7.5
    //# If the algorithm suite has a signature algorithm, this operation MUST
    //# verify the message footer using the specified signature algorithm.

    
    //= compliance/client-apis/decrypt.txt#2.7
    //# ./framework/algorithm-
    //# suites.md#signature-algorithm), this operation MUST perform
    //# this step.
    var signature :- SerializeFunctions
    
      //= compliance/client-apis/decrypt.txt#2.7.5
      //# After deserializing the body, this operation MUST deserialize the
      //# next encrypted message bytes as the message footer (../data-format/
      //# message-footer.md).
      .ReadShortLengthSeq(buffer)
      .MapFailure(MapSerializeFailure(": ReadShortLengthSeq"));

    var ecdsaParams := Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.curve;

    //= compliance/client-apis/decrypt.txt#2.7.5
    //# Once the message footer is deserialized, this operation MUST use the
    //# signature algorithm (../framework/algorithm-suites.md#signature-
    //# algorithm) from the algorithm suite (../framework/algorithm-
    //# suites.md) in the decryption materials to verify the encrypted
    //# message, with the following inputs:
    var signatureVerifiedResult :- Signature.Verify(ecdsaParams,
      //#*  The verification key is the verification key (../framework/
      //#   structures.md#verification-key) in the decryption materials.
      decMat.verificationKey.value,
      //#*  The input to verify is the concatenation of the serialization of
      //#   the message header (../data-format/message-header.md) and message
      //#   body (../data-format/message-body.md).
      msg,
      signature.data
    );

    return Success(signature.tail);
  }

  predicate {:opaque } SignatureBySequence(signature: seq<uint8>, sequence: seq<uint8>)
  {
    && |signature| < UINT16_LIMIT
    && sequence == UInt16ToSeq(|signature| as uint16) + signature
  }

  lemma UpperBoundRemv(sequence: seq<uint8>, lo: int)
    requires 0 <= lo <= |sequence|
    ensures sequence[lo..|sequence|] == sequence[lo..]
  {

  }

  lemma LemmaESDKAlgorithmSuiteIdImpliesEquality(
    esdkId: SerializableTypes.ESDKAlgorithmSuiteId,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    requires SerializableTypes.GetAlgorithmSuiteId(esdkId) == suite.id
    ensures
      && var suiteId := SerializableTypes.GetAlgorithmSuiteId(esdkId);
      && Client.SpecificationClient().GetSuite(suiteId) == suite
  {
    var suiteId := SerializableTypes.GetAlgorithmSuiteId(esdkId);
    if Client.SpecificationClient().GetSuite(suiteId) != suite {
      assert Client.SpecificationClient().GetSuite(suiteId).encrypt.keyLength == suite.encrypt.keyLength;
    }
  }

  function method MapSerializeFailure(s: string): SerializeFunctions.ReadProblems -> string {
    (e: SerializeFunctions.ReadProblems) =>
    match e
      case Error(e) => e
      case MoreNeeded(_) => "Incomplete message" + s
  }

}
