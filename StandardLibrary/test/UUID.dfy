// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/UUID.dfy"

module TestUUID {
  import opened UUID
  import opened UInt = StandardLibrary.UInt

  const uuid := "92382658-b7a0-4d97-9c49-cee4e672a3b3";
  const byteUuid: seq<uint8> := [146, 56, 38, 88,
                                183, 160, 77, 151,
                                156, 73, 206, 228, 
                                230, 114, 163, 179];
  
  const wrongByteUuid: seq<uint8> := [146, 56, 38, 88,
                                183, 160, 77, 151,
                                156, 73, 206, 228, 
                                230, 114, 163, 178];
  
  method {:test} TestFromBytesSuccess() {
    var fromBytes :- expect UUID.FromByteArray(byteUuid);
    expect fromBytes == uuid;
  }

  method {:test} TestFromBytesFailure() {
    var fromBytes :- expect UUID.FromByteArray(wrongByteUuid);
    expect fromBytes != uuid;
  }

  method {:test} TestToBytesSuccess() {
    var toBytes :- expect UUID.ToByteArray(uuid);
    expect toBytes == byteUuid;
  }
  
  method {:test} TestToBytesFailure() {
    var toBytes :- expect UUID.ToByteArray(uuid);
    expect toBytes != wrongByteUuid;
  }

  method {:test} TestRoundTripStringConversion() {
    var stringToBytes :- expect UUID.ToByteArray(uuid);
    expect |stringToBytes| == 16;
    var bytesToString :- expect UUID.FromByteArray(stringToBytes);
    expect bytesToString == uuid;
  }

  method {:test} TestRoundTripByteConversion() {
    var bytesToString :- expect UUID.FromByteArray(byteUuid);
    var stringToBytes :- expect UUID.ToByteArray(bytesToString);
    expect |stringToBytes| == 16;
    expect stringToBytes == byteUuid;
  }

  method {:test} TestGenerateAndConversion() {
    var uuidString :- expect UUID.GenerateUUID();
    var uuidBytes :- expect UUID.ToByteArray(uuidString);

    var bytesToString :- expect UUID.FromByteArray(uuidBytes);
    var stringToBytes :- expect UUID.ToByteArray(bytesToString);
    expect |stringToBytes| == 16;
    expect stringToBytes == uuidBytes;

    var uuidStringToBytes :- expect UUID.ToByteArray(uuidString);
    expect |uuidStringToBytes| == 16;
    var uuidBytesToString :- expect UUID.FromByteArray(uuidStringToBytes);
    expect uuidBytesToString == uuidString;
  }
}