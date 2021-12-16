// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"

module EncryptedDataKeys {
  import Aws.Crypto
  import Seq
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  function method WriteEncryptedDataKey(edk: ESDKEncryptedDataKey): (ret: seq<uint8>)
  {
    WriteShortLengthSeq(edk.keyProviderId)
    + WriteShortLengthSeq(edk.keyProviderInfo)
    + WriteShortLengthSeq(edk.ciphertext)
  }

  function method {:tailrecursion} WriteEncryptedDataKeys(
    edks: ESDKEncryptedDataKeys
  ):
    (ret: seq<uint8>)
    ensures |edks| == 0 ==> ret == []
    ensures |edks| != 0
    ==>
      WriteEncryptedDataKeys(Seq.DropLast(edks))
        + WriteEncryptedDataKey(Seq.Last(edks))
      == ret
  {
    if |edks| == 0 then []
    else
      WriteEncryptedDataKeys(Seq.DropLast(edks)) + WriteEncryptedDataKey(Seq.Last(edks))
  }

  function method WriteEncryptedDataKeysSection(
    edks: ESDKEncryptedDataKeys
  ):
    (ret: seq<uint8>)
  {
    UInt16ToSeq(|edks| as uint16) + WriteEncryptedDataKeys(edks)
  }

  function method ReadEncryptedDataKey(
    bytes: ReadableBytes
  ):
    (res: ReadCorrect<ESDKEncryptedDataKey>)
    ensures CorrectlyRead(bytes, res, WriteEncryptedDataKey)
  {
    var Data(providerId, providerIdPos) :- ReadShortLengthSeq(bytes);
    :- Need(ValidUTF8Seq(providerId), Error("Invalid providerID"));
    var Data(providerInfo, providerInfoPos) :- ReadShortLengthSeq(providerIdPos);
    var Data(cipherText, tail) :- ReadShortLengthSeq(providerInfoPos);
    var edk: ESDKEncryptedDataKey := Crypto.EncryptedDataKey(
        keyProviderId := providerId,
        keyProviderInfo := providerInfo,
        ciphertext := cipherText);

    Success(Data(edk, tail))
  }

  function method {:tailrecursion true} ReadEncryptedDataKeys(
    bytes: ReadableBytes,
    accumulator: ESDKEncryptedDataKeys,
    count: uint16,
    nextEdkStart: ReadableBytes
  )
    :(res: ReadCorrect<ESDKEncryptedDataKeys>)
    requires 0 <= |accumulator| <= count as nat < UINT16_LIMIT
    requires CorrectlyRead(bytes, Success(Data(accumulator, nextEdkStart)), WriteEncryptedDataKeys)
    decreases count as int - |accumulator|
    ensures CorrectlyRead(bytes, res, WriteEncryptedDataKeys)
    ensures res.Success? ==> count as nat == |res.value.thing|
  {
    if count as int > |accumulator| then
      var Data(edk, newPos) :- ReadEncryptedDataKey(nextEdkStart);
      var nextAcc := accumulator + [edk];
      ReadEncryptedDataKeys(bytes, nextAcc, count, newPos)
    else
      Success(Data(accumulator, nextEdkStart))
  }

  function method ReadEncryptedDataKeysSection(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<ESDKEncryptedDataKeys>)
    ensures CorrectlyRead(bytes, res, WriteEncryptedDataKeysSection)
  {
    var Data(count, edkStart) :- ReadUInt16(bytes);
    :- Need(count > 0, Error("Invalid Encrypted Data Keys section: 0 EDKs is not valid."));
    var Data(edks, tail) :- ReadEncryptedDataKeys(edkStart, [], count, edkStart);
    Success(Data(edks, tail))
  }
}
