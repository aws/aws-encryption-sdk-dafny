// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Streams.dfy"

module TestStreams {
  import opened UInt = StandardLibrary.UInt
  import opened Streams

  method {:test} TestSeqReaderReadElements() {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res := reader.ReadElements(3);
    expect [0, 100, 200] == res;

    res := reader.ReadElements(0);
    expect [] == res;

    res := reader.ReadElements(2);
    expect [300, 400] == res;
  }

  method {:test} TestSeqReaderReadExact() {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res :- expect reader.ReadExact(3);
    expect [0, 100, 200] == res;

    res :- expect reader.ReadExact(0);
    expect [] == res;

    res :- expect reader.ReadExact(2);
    expect [300, 400] == res;

    var isFailure := reader.ReadExact(1);
    expect isFailure.Failure?;
  }

  method {:test} TestByteReader() {
    var s: seq<uint8> := [0, 3, 10, 20, 50, 100, 150, 200, 250, 255];
    var reader := new Streams.ByteReader(s);

    var uint8Res :- expect reader.ReadByte();
    var sizeRead := reader.GetSizeRead();
    var isDoneReading := reader.IsDoneReading();
    expect 0 == uint8Res;
    expect 1 == sizeRead;
    expect !isDoneReading;

    var sRes :- expect reader.ReadBytes(0);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect [] == sRes;
    expect 1 == sizeRead;
    expect !isDoneReading;

    sRes :- expect reader.ReadBytes(3);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect [3, 10, 20] == sRes;
    expect 4 == sizeRead;
    expect !isDoneReading;

    var uint16 :- expect reader.ReadUInt16();
    var expectedUint16 := SeqToUInt16([50, 100]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect expectedUint16 == uint16;
    expect 6 == sizeRead;
    expect !isDoneReading;

    var uint32 :- expect reader.ReadUInt32();
    var expectedUint32 := SeqToUInt32([150, 200, 250, 255]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect expectedUint32 == uint32;
    expect 10 == sizeRead;
    expect isDoneReading;

    var isByteFailure := reader.ReadByte();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect isByteFailure.Failure?;
    expect 10 == sizeRead;
    expect isDoneReading;

    var isBytesFailure := reader.ReadBytes(1);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect isBytesFailure.Failure?;
    expect 10 == sizeRead;
    expect isDoneReading;

    var isUint16Failure := reader.ReadUInt16();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect isUint16Failure.Failure?;
    expect 10 == sizeRead;
    expect isDoneReading;

    var isUint32Failure := reader.ReadUInt32();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    expect isUint32Failure.Failure?;
    expect 10 == sizeRead;
    expect isDoneReading;
  }

  method {:test} TestSeqWriter() {
    var writer := new Streams.SeqWriter<nat>();
    expect [] == writer.data;

    var elemSize := writer.WriteElements([]);
    expect 0 == elemSize;
    expect [] == writer.data;

    elemSize := writer.WriteElements([0, 100, 200]);
    expect 3 == elemSize;
    expect [0, 100, 200] == writer.data;

    elemSize := writer.WriteElements([300, 400, 500, 600]);
    expect 4 == elemSize;
    expect [0, 100, 200, 300, 400, 500, 600] == writer.data;
  }

  method {:test} TestByteWriter() {
    var writer := new Streams.ByteWriter();
    var dataWritten := writer.GetDataWritten();
    expect [] == dataWritten;
    var sizeWritten := writer.GetSizeWritten();
    expect 0 == sizeWritten;

    var res := writer.WriteByte(0);
    expect 1 == res;
    dataWritten := writer.GetDataWritten();
    expect [0] == dataWritten;
    sizeWritten := writer.GetSizeWritten();
    expect 1 == sizeWritten;

    res := writer.WriteBytes([]);
    expect 0 == res;
    dataWritten := writer.GetDataWritten();
    expect [0] == dataWritten;
    sizeWritten := writer.GetSizeWritten();
    expect 1 == sizeWritten;

    res := writer.WriteBytes([5, 50, 100]);
    expect 3 == res;
    dataWritten := writer.GetDataWritten();
    expect [0, 5, 50, 100] == dataWritten;
    sizeWritten := writer.GetSizeWritten();
    expect 4 == sizeWritten;

    var uint16Written := SeqToUInt16([150, 200]);
    res := writer.WriteUInt16(uint16Written);
    expect 2 == res;
    dataWritten := writer.GetDataWritten();
    expect [0, 5, 50, 100, 150, 200] == dataWritten;
    sizeWritten := writer.GetSizeWritten();
    expect 6 == sizeWritten;

    var uint32Written := SeqToUInt32([50, 150, 200, 255]);
    res := writer.WriteUInt32(uint32Written);
    expect 4 == res;
    dataWritten := writer.GetDataWritten();
    expect [0, 5, 50, 100, 150, 200, 50, 150, 200, 255] == dataWritten;
    sizeWritten := writer.GetSizeWritten();
    expect 10 == sizeWritten;
  }
}
