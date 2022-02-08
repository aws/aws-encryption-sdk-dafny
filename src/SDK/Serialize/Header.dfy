// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "EncryptionContext.dfy"

include "V1HeaderBody.dfy"
include "V2HeaderBody.dfy"
include "HeaderTypes.dfy"
include "HeaderAuth.dfy"
include "SharedHeaderFunctions.dfy"


module Header {
  import Aws.Crypto
  import Seq
  import MaterialProviders.Client
  import EncryptionContext

  import V1HeaderBody
  import V2HeaderBody
  import HeaderTypes
  import HeaderAuth
  import SharedHeaderFunctions

  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

datatype HeaderInfo = HeaderInfo(
    nameonly body: HeaderTypes.HeaderBody,
    nameonly rawHeader: seq<uint8>,
    nameonly encryptionContext: ESDKEncryptionContext,
    nameonly suite: Client.AlgorithmSuites.AlgorithmSuite,
    nameonly headerAuth: HeaderTypes.HeaderAuth
  )

  predicate IsHeader(h: HeaderInfo)
  {
    && GetESDKAlgorithmSuiteId(h.suite.id) == h.body.esdkSuiteId
    // TODO: Even though we're not yet supporting non-framed content,
    // this assertion about non-framed messages has ripple effects on
    // other proofs
    && h.body.contentType.NonFramed? <==> 0 == h.body.frameLength
    && h.body.contentType.Framed? <==> 0 < h.body.frameLength
    && HeaderAuth?(h.suite, h.headerAuth)
    && HeaderVersionSupportsCommitment?(h.suite, h.body)
    // There are 2 readable formats, but only 1 writeable format.
    // This means that a correct header is defined by reading.
    // Less options to keep track of.
    && CorrectlyReadHeaderBody(
      ReadableBuffer(h.rawHeader, 0), 
      Success(SuccessfulRead(h.body, ReadableBuffer(h.rawHeader, |h.rawHeader|))))
    // I would like to have this relationship, but the CMM really gets to control this
    // So I'm going to push towards this distinguishing the stored vs the "complete" encryption context.
    // && h.encryptionContext == EncryptionContext.GetEncryptionContext(h.body.encryptionContext)
  }

  predicate HeaderAuth?(
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    headerAuth: HeaderTypes.HeaderAuth
  )
  {
      && (headerAuth.AESMac?
    ==>
      && |headerAuth.headerIv| == suite.encrypt.ivLength as nat
      && |headerAuth.headerAuthTag| == suite.encrypt.tagLength as nat)
  }

  predicate method HeaderVersionSupportsCommitment?(
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    body: HeaderTypes.HeaderBody
  )
  {
    && (suite.commitment.HKDF?
      ==>
        && body.V2HeaderBody?
        && |body.suiteData| == suite.commitment.outputKeyLength as nat)
    && (!suite.commitment.HKDF?
      ==>
        && body.V1HeaderBody?)
  }

  type Header = h: HeaderInfo
  | IsHeader(h)
  witness *

  function method ReadHeaderBody(
     buffer: ReadableBuffer,
     maxEdks: int64
  )
    :(res: ReadCorrect<HeaderTypes.HeaderBody>)
    ensures CorrectlyReadHeaderBody(buffer, res)
  {

    var version :- SharedHeaderFunctions.ReadMessageFormatVersion(buffer);

    match version.data
    case V1 => 
      var b :- V1HeaderBody.ReadV1HeaderBody(buffer, maxEdks);
      var body: HeaderTypes.HeaderBody := b.data;
      Success(SuccessfulRead(body, b.tail))
    case V2 => 
      var b :- V2HeaderBody.ReadV2HeaderBody(buffer, maxEdks);
      var body: HeaderTypes.HeaderBody := b.data;
      Success(SuccessfulRead(body, b.tail))
  }

  predicate CorrectlyReadHeaderBody(
    buffer: ReadableBuffer,
    res: ReadCorrect<HeaderTypes.HeaderBody>
  )
  {
    res.Success?
    ==>
    && CorrectlyReadRange(buffer, res.value.tail)
    && match res.value.data
      case V1HeaderBody(_,_,_,_,_,_,_,_) =>
        V1HeaderBody.CorrectlyReadV1HeaderBody(buffer, res)
      case V2HeaderBody(_,_,_,_,_,_,_) =>
        V2HeaderBody.CorrectlyReadV2HeaderBody(buffer, res)
  }

  function method WriteHeaderBody(
    body: HeaderTypes.HeaderBody
  )
    :(ret: seq<uint8>)
  {
    match body
    case V1HeaderBody(_,_,_,_,_,_,_,_) =>
      V1HeaderBody.WriteV1HeaderBody(body)
    case V2HeaderBody(_,_,_,_,_,_,_) =>
      V2HeaderBody.WriteV2HeaderBody(body)
  }

}
