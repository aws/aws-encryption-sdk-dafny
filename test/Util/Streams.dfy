include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Streams.dfy"

module TestStreams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Streams

  method {:test} TestSeqReaderReadElements() returns (r: TestResult) {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res := reader.ReadElements(3);
    :- RequireEqual([0, 100, 200], res);

    res := reader.ReadElements(0);
    :- RequireEqual([], res);

    res := reader.ReadElements(2);
    r := RequireEqual([300, 400], res);
  }

  method {:test} TestSeqReaderReadExact() returns (r: TestResult) {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res :- reader.ReadExact(3);
    :- RequireEqual([0, 100, 200], res);

    res :- reader.ReadExact(0);
    :- RequireEqual([], res);

    res :- reader.ReadExact(2);
    :- RequireEqual([300, 400], res);

    var isFailure := reader.ReadExact(1);
    r := RequireFailure(isFailure);
  }

  method {:test} TestByteReader() returns (r: TestResult) {
    var s: seq<uint8> := [0, 3, 10, 20, 50, 100, 150, 200, 250, 255];
    var reader := new Streams.ByteReader(s);

    var uint8Res :- reader.ReadByte();
    var sizeRead := reader.GetSizeRead();
    var isDoneReading := reader.IsDoneReading();
    :- RequireEqual(0, uint8Res);
    :- RequireEqual(1, sizeRead);
    :- Require(!isDoneReading);

    var sRes :- reader.ReadBytes(0);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireEqual([], sRes);
    :- RequireEqual(1, sizeRead);
    :- Require(!isDoneReading);

    sRes :- reader.ReadBytes(3);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireEqual([3, 10, 20], sRes);
    :- RequireEqual(4, sizeRead);
    :- Require(!isDoneReading);

    var uint16 :- reader.ReadUInt16();
    var expectedUint16 := SeqToUInt16([50, 100]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireEqual(expectedUint16, uint16);
    :- RequireEqual(6, sizeRead);
    :- Require(!isDoneReading);

    var uint32 :- reader.ReadUInt32();
    var expectedUint32 := SeqToUInt32([150, 200, 250, 255]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireEqual(expectedUint32, uint32);
    :- RequireEqual(10, sizeRead);
    :- Require(isDoneReading);

    var isByteFailure := reader.ReadByte();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireFailure(isByteFailure);
    :- RequireEqual(10, sizeRead);
    :- Require(isDoneReading);

    var isBytesFailure := reader.ReadBytes(1);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireFailure(isBytesFailure);
    :- RequireEqual(10, sizeRead);
    :- Require(isDoneReading);

    var isUint16Failure := reader.ReadUInt16();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireFailure(isUint16Failure);
    :- RequireEqual(10, sizeRead);
    :- Require(isDoneReading);

    var isUint32Failure := reader.ReadUInt32();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    :- RequireFailure(isUint32Failure);
    :- RequireEqual(10, sizeRead);
    r := Require(isDoneReading);
  }

  method {:test} TestSeqWriter() returns (r: TestResult) {
    var writer := new Streams.SeqWriter<nat>();
    :- RequireEqual([], writer.data);

    var elemSize := writer.WriteElements([]);
    :- RequireEqual(0, elemSize);
    :- RequireEqual([], writer.data);

    elemSize := writer.WriteElements([0, 100, 200]);
    :- RequireEqual(3, elemSize);
    :- RequireEqual([0, 100, 200], writer.data);

    elemSize := writer.WriteElements([300, 400, 500, 600]);
    :- RequireEqual(4, elemSize);
    r := RequireEqual([0, 100, 200, 300, 400, 500, 600], writer.data);
  }

  method {:test} TestByteWriter() returns (r: TestResult) {
    var writer := new Streams.ByteWriter();
    var dataWritten := writer.GetDataWritten();
    :- RequireEqual([], dataWritten);
    var sizeWritten := writer.GetSizeWritten();
    :- RequireEqual(0, sizeWritten);

    var res := writer.WriteByte(0);
    :- RequireEqual(1, res);
    dataWritten := writer.GetDataWritten();
    :- RequireEqual([0], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    :- RequireEqual(1, sizeWritten);

    res := writer.WriteBytes([]);
    :- RequireEqual(0, res);
    dataWritten := writer.GetDataWritten();
    :- RequireEqual([0], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    :- RequireEqual(1, sizeWritten);

    res := writer.WriteBytes([5, 50, 100]);
    :- RequireEqual(3, res);
    dataWritten := writer.GetDataWritten();
    :- RequireEqual([0, 5, 50, 100], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    :- RequireEqual(4, sizeWritten);

    var uint16Written := SeqToUInt16([150, 200]);
    res := writer.WriteUInt16(uint16Written);
    :- RequireEqual(2, res);
    dataWritten := writer.GetDataWritten();
    :- RequireEqual([0, 5, 50, 100, 150, 200], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    :- RequireEqual(6, sizeWritten);

    var uint32Written := SeqToUInt32([50, 150, 200, 255]);
    res := writer.WriteUInt32(uint32Written);
    :- RequireEqual(4, res);
    dataWritten := writer.GetDataWritten();
    :- RequireEqual([0, 5, 50, 100, 150, 200, 50, 150, 200, 255], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    r := RequireEqual(10, sizeWritten);
  }
}
