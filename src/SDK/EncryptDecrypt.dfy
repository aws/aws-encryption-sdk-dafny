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
      res.value == SerializeMessageWithoutSignature(framedMessage, suite).value + WriteShortLengthSeq(signature)
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
    requires Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat)
    // TODO: Add Proof
    // ensures match res
    //   case Failure(_) => true
    //   case Success(_) =>
    //     && 2 <= old(rd.reader.pos) + 2 <= rd.reader.pos
    //     && SignatureBySequence(signature, rd.reader.data[old(rd.reader.pos)..rd.reader.pos])
  {

    // DecryptionMaterialsWithPlaintextDataKey ensures that the materials and the suite match.
    // If there is no verification key, that lets us conclude that the suite does not have a signature.
    if decMat.verificationKey.None? {
      return Success(buffer);
    }

    var signature :- SerializeFunctions
      .ReadShortLengthSeq(buffer)
      .MapFailure(MapSerializeFailure(": ReadShortLengthSeq"));

    var ecdsaParams := Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.curve;
    // verify signature
    var signatureVerifiedResult :- Signature.Verify(ecdsaParams, decMat.verificationKey.value, msg, signature.data);

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
