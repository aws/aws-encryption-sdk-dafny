// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module Serialize {
  import opened Seq
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8

  type ShortByteSeq = s: seq<uint8> | |s| < UINT16_LIMIT
  type ShortUtf8Seq = s: ValidUTF8Bytes | |s| < UINT16_LIMIT

  datatype EncryptedDataKey = EncryptedDataKey(providerID: ShortUtf8Seq,
                                               providerInfo: ShortByteSeq,
                                               ciphertext: ShortByteSeq)

  type EncryptedDataKeys = s: seq<EncryptedDataKey> | |s| < UINT16_LIMIT

  function method EncryptedDataKeysToSeq(edks: EncryptedDataKeys):  (ret: seq<uint8>)
  {
    UInt16ToSeq(|edks| as uint16) + FoldLeft(FoldEncryptedDataKey, [], edks)
  }

  function method FoldEncryptedDataKey(acc: seq<uint8>, edk: EncryptedDataKey): (ret: seq<uint8>)
  {
      acc
        + UInt16ToSeq(|edk.providerID| as uint16) + edk.providerID
        + UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo
        + UInt16ToSeq(|edk.ciphertext| as uint16) + edk.ciphertext
  }

  function method ReadShortLengthSeq(
    s: seq<uint8>,
    pos: nat
  ): (
    Result<Option<(ShortByteSeq, nat)>, string>
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

  function method ReadEncryptedDataKey(s: seq<uint8>, pos: nat): Result<Option<(EncryptedDataKey, nat)>, string> {
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
                  providerID,
                  providerInfo,
                  cipherText
                ), readCipherText)))
            }
        }
    }
  }

  function method ReadEncryptedDataKeyRecursive(s: seq<uint8>, pos: nat, remaining: uint16): (ret: Result<Option<(EncryptedDataKeys, nat)>, string>)
    decreases remaining
    ensures match ret
      case Success(Some((edks, _))) => |edks| == remaining as int
      case _ => true
  {
    match remaining {
      case 0 =>
        var r : EncryptedDataKeys := [];
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
                var edks : EncryptedDataKeys := [edk] + restEDKs;
                Success(Some((edks, restPos)))
            }
        }
    }
  }

  function method EncryptedDataKeysFromSeq(s: seq<uint8>, pos: nat): Result<Option<(EncryptedDataKeys, nat)>, string> {
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
