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

  type Header = h: HeaderInfo
  |
    && GetESDKAlgorithmSuiteId(h.suite.id) == h.body.esdkSuiteId
    && h.body.contentType.NonFramed? <==> 0 == h.body.frameLength
    && h.body.contentType.Framed? <==> 0 < h.body.frameLength
    && (h.headerAuth.AESMac?
    ==>
      && |h.headerAuth.headerIv| == h.suite.encrypt.ivLength as nat
      && |h.headerAuth.headerAuthTag| == h.suite.encrypt.tagLength as nat)
    && (h.suite.commitment.HKDF?
      ==>
        && h.body.V2HeaderBody?
        && |h.body.suiteData| == h.suite.commitment.outputKeyLength as nat)
    && (!h.suite.commitment.HKDF?
      ==>
        && h.body.V1HeaderBody?)
    && CorrectlyReadHeaderBody(h.body, ReadableBytes(h.rawHeader, 0))
  witness *

  function method ReadHeaderBody(
     bytes: ReadableBytes
  )
    :(res: ReadCorrect<HeaderTypes.HeaderBody>)
    ensures res.Success? ==> CorrectlyReadHeaderBody(res.value.thing, bytes)
  {

    var version :- SharedHeaderFunctions.ReadMessageFormatVersion(bytes);

    match version.thing
    case V1 => 
      var b :- V1HeaderBody.ReadV1HeaderBody(bytes);
      var body: HeaderTypes.HeaderBody := b.thing;
      Success(Data(body, b.tail))
    case V2 => 
      var b :- V2HeaderBody.ReadV2HeaderBody(bytes);
      var body: HeaderTypes.HeaderBody := b.thing;
      Success(Data(body, b.tail))
  }

  predicate CorrectlyReadHeaderBody(
    body: HeaderTypes.HeaderBody,
    bytes: ReadableBytes
  )
  {
    match body
    case V1HeaderBody(_,_,_,_,_,_,_,_) =>
      V1HeaderBody.CorrectlyReadV1HeaderBody(bytes, Success(Data(body, bytes)))
    case V2HeaderBody(_,_,_,_,_,_,_) =>
      V2HeaderBody.CorrectlyReadV2HeaderBody(bytes, Success(Data(body, bytes)))
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
