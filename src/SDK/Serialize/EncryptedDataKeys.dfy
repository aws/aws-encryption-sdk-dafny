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
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<ESDKEncryptedDataKey>)
    ensures CorrectlyRead(s, pos, res, WriteEncryptedDataKey)
  {
    var (providerId, providerIdPos) :- ReadShortLengthSeq(s, pos);
    :- Need(ValidUTF8Seq(providerId), Error("Invalid providerID"));
    var (providerInfo, providerInfoPos) :- ReadShortLengthSeq(s, providerIdPos);
    var (cipherText, cipherTextPos) :- ReadShortLengthSeq(s, providerInfoPos);
    var edk: ESDKEncryptedDataKey := Crypto.EncryptedDataKey(
        keyProviderId := providerId,
        keyProviderInfo := providerInfo,
        ciphertext := cipherText);

    Success((edk, cipherTextPos))
  }

  function method {:tailrecursion true} ReadEncryptedDataKeys(
    s: seq<uint8>,
    pos: nat,
    accumulator: ESDKEncryptedDataKeys,
    count: uint16,
    nextEdk: nat
  ):
    (res: ReadCorrect<ESDKEncryptedDataKeys>)
    requires 0 <= |accumulator| <= count as nat < UINT16_LIMIT
    requires |s| >= nextEdk >= pos
    requires WriteEncryptedDataKeys(accumulator) == s[pos..nextEdk]
    decreases count as int - |accumulator|
    ensures CorrectlyRead(s, pos, res, WriteEncryptedDataKeys)
    ensures res.Success? ==> count as nat == |res.value.0|
  {
    if count as int > |accumulator| then
      var (edk, newPos) :- ReadEncryptedDataKey(s, nextEdk);
      var nextAcc := accumulator + [edk];
      ReadEncryptedDataKeys(s, pos, nextAcc, count, newPos)
    else
      Success((accumulator, nextEdk))
  }

  function method ReadEncryptedDataKeysSection(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<ESDKEncryptedDataKeys>)
    ensures CorrectlyRead(s, pos, res, WriteEncryptedDataKeysSection)
  {
    var (count, edkStart) :- ReadUInt16(s, pos);
    :- Need(count > 0, Error("Invalid Encrypted Data Keys section: 0 EDKs is not valid."));
    var (edks, end) :- ReadEncryptedDataKeys(s, edkStart, [], count, edkStart);
    Success((edks, end))
  }
}
