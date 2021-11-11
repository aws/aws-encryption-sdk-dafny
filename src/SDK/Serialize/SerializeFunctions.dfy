// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"

module SerializeFunctions {
  import opened Aws.Crypto
  import opened Seq
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8

  function method EncryptedDataKeysToSeq(edks: ESDKEncryptedDataKeys):  (ret: seq<uint8>)
  {
    UInt16ToSeq(|edks| as uint16) + FoldLeft(FoldEncryptedDataKey, [], edks)
  }

  function method FoldEncryptedDataKey(acc: seq<uint8>, edk: ESDKEncryptedDataKey): (ret: seq<uint8>)
  {
      acc
        + UInt16ToSeq(|edk.keyProviderId| as uint16) + edk.keyProviderId
        + UInt16ToSeq(|edk.keyProviderInfo| as uint16) + edk.keyProviderInfo
        + UInt16ToSeq(|edk.ciphertext| as uint16) + edk.ciphertext
  }

  function method ReadShortLengthSeq(
    s: seq<uint8>,
    pos: nat
  ): (
    Result<Option<(Uint8Seq16, nat)>, string>
  ) {
    if |s| >= pos+2 then
      var length := SeqToUInt16(s[pos..2+pos]) as nat;
      if |s| >= pos+2+length then
        Success(Some((s[2+pos..2+pos+length], 2+pos+length)))
      else
        Success(None)
    else
      Success(None)
  }

  function method ReadEncryptedDataKey(s: seq<uint8>, pos: nat): Result<Option<(ESDKEncryptedDataKey, nat)>, string> {
    var providerIDM :- ReadShortLengthSeq(s, pos);
    match providerIDM {
      case None => Success(None)
      case Some((providerID, readProviderID)) =>
        :- Need(ValidUTF8Seq(providerID), "Invalid providerID");
        var providerInfoM :- ReadShortLengthSeq(s, readProviderID);
        match providerIDM {
          case None => Success(None)
          case Some((providerInfo, readProviderInfo)) =>
            var cipherTextM :- ReadShortLengthSeq(s, readProviderInfo);
            match cipherTextM {
              case None => Success(None)
              case Some((cipherText, readCipherText)) =>
                Success(Some((EncryptedDataKey(
                  keyProviderId := providerID,
                  keyProviderInfo := providerInfo,
                  ciphertext := cipherText
                ), readCipherText)))
            }
        }
    }
  }

  function method ReadEncryptedDataKeyRecursive(s: seq<uint8>, pos: nat, remaining: uint16): (ret: Result<Option<(ESDKEncryptedDataKeys, nat)>, string>)
    decreases remaining
    ensures match ret
      case Success(Some((edks, _))) => |edks| == remaining as int
      case _ => true
  {
    match remaining {
      case 0 =>
        var r : ESDKEncryptedDataKeys := [];
        Success(Some((r, pos)))
      case _ =>
        var edkM :- ReadEncryptedDataKey(s, pos);
        match edkM {
          case None => Success(None)
          case Some((edk, newPos)) =>
            var restM :- ReadEncryptedDataKeyRecursive(s, newPos, remaining - 1);
            match restM {
              case None =>
                Success(None)
              case Some((restEDKs, restPos)) =>
                var edks : ESDKEncryptedDataKeys := [edk] + restEDKs;
                Success(Some((edks, restPos)))
            }
        }
    }
  }

  function method EncryptedDataKeysFromSeq(s: seq<uint8>, pos: nat): Result<Option<(ESDKEncryptedDataKeys, nat)>, string> {
    if |s| >= pos+2 then
      var count := SeqToUInt16(s[pos..2+pos]);
      if count == 0 then
        Failure("Invalid EDKs seq")
      else
        ReadEncryptedDataKeyRecursive(s, pos+2, count)
    else
      Success(None)
  }
}
