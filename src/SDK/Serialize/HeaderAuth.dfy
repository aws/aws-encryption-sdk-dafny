// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "HeaderTypes.dfy"
include "EncryptionContext.dfy"
include "EncryptedDataKeys.dfy"

module HeaderAuth {
  import Aws.Crypto
  import Seq
  import HeaderTypes
  import MaterialProviders.Client
  import opened EncryptedDataKeys
  import opened EncryptionContext
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  type AESMac = a: HeaderTypes.HeaderAuth
  | a.AESMac?
  witness *

  function method WriteHeaderAuthTagV2(
    headerAuth: AESMac
  )
    :(ret: seq<uint8>)
  {
    Write(headerAuth.headerAuthTag)
  }

  function method WriteHeaderAuthTagV1(
    headerAuth: AESMac
  )
    :(ret: seq<uint8>)
  {
    Write(headerAuth.headerIv) + Write(headerAuth.headerAuthTag)
  }

  function method WriteHeaderAuthTag(
    headerAuth: AESMac,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(ret: Result<seq<uint8>, string>)
  {
    match suite.messageVersion
      case 1 => Success(WriteHeaderAuthTagV1(headerAuth))
      case 2 => Success(WriteHeaderAuthTagV2(headerAuth))
      case _ => Failure("Unexpected message version")
  }

  function method ReadHeaderAuthTagV1(
    buffer: ReadableBuffer,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: ReadCorrect<AESMac>)
    ensures CorrectlyRead(buffer, res, WriteHeaderAuthTagV1)
    ensures res.Success?
    ==>
      && |res.value.data.headerIv| == suite.encrypt.ivLength as nat
      && |res.value.data.headerAuthTag| == suite.encrypt.tagLength as nat
  {
    var headerIv :- Read(buffer, suite.encrypt.ivLength as nat);
    var headerAuthTag :- Read(headerIv.tail, suite.encrypt.tagLength as nat);

    var auth: AESMac := HeaderTypes.HeaderAuth.AESMac(
      headerIv := headerIv.data,
      headerAuthTag := headerAuthTag.data
    );

    Success(SuccessfulRead(auth, headerAuthTag.tail))
  }

  function method ReadHeaderAuthTagV2(
    buffer: ReadableBuffer,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: ReadCorrect<AESMac>)
    ensures CorrectlyRead(buffer, res, WriteHeaderAuthTagV2)
    ensures res.Success?
    ==>
      && |res.value.data.headerIv| == suite.encrypt.ivLength as nat
      && |res.value.data.headerAuthTag| == suite.encrypt.tagLength as nat
  {
    // TODO: probably this hardcoded iv of all 0s will go into alg suite
    var headerIv := seq(suite.encrypt.ivLength as int, _ => 0);
    var headerAuthTag :- Read(buffer, suite.encrypt.tagLength as nat);

    var auth: AESMac := HeaderTypes.HeaderAuth.AESMac(
      headerIv := headerIv,
      headerAuthTag := headerAuthTag.data
    );

    Success(SuccessfulRead(auth, headerAuthTag.tail))
  }


  function method ReadHeaderAuthTag(
    buffer: ReadableBuffer,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: ReadCorrect<AESMac>)
    ensures suite.messageVersion == 1 ==> CorrectlyRead(buffer, res, WriteHeaderAuthTagV1)
    ensures suite.messageVersion == 2 ==> CorrectlyRead(buffer, res, WriteHeaderAuthTagV2)
    ensures res.Success?
    ==>
      && |res.value.data.headerIv| == suite.encrypt.ivLength as nat
      && |res.value.data.headerAuthTag| == suite.encrypt.tagLength as nat
  {
    match suite.messageVersion
      case 1 => ReadHeaderAuthTagV1(buffer, suite)
      case 2 => ReadHeaderAuthTagV2(buffer, suite)
      case _ => Failure(Error("Unexpected message version"))
  }
}
