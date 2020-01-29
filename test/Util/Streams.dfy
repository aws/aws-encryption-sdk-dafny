include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Streams.dfy"

module TestStreams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Streams

  method {:test} TestSeqReaderReadElements() returns (r: Result<()>) {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res := reader.ReadElements(3);
    var _ :- RequireEqual([0, 100, 200], res);

    res := reader.ReadElements(0);
    var _ :- RequireEqual([], res);

    res := reader.ReadElements(2);
    r := RequireEqual([300, 400], res);
  }

  method {:test} TestSeqReaderReadExact() returns (r: Result<()>) {
    var s: seq<nat> := [0, 100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res :- reader.ReadExact(3);
    var _ :- RequireEqual([0, 100, 200], res);

    res :- reader.ReadExact(0);
    var _ :- RequireEqual([], res);

    res :- reader.ReadExact(2);
    var _ :- RequireEqual([300, 400], res);

    var isFailure := reader.ReadExact(1);
    r := RequireFailure(isFailure);
  }

  method {:test} TestByteReader() returns (r: Result<()>) {
    var s: seq<uint8> := [0, 3, 10, 20, 50, 100, 150, 200, 250, 255];
    var reader := new Streams.ByteReader(s);

    var uint8Res :- reader.ReadByte();
    var sizeRead := reader.GetSizeRead();
    var isDoneReading := reader.IsDoneReading();
    var _ :- RequireEqual(0, uint8Res);
    var _ :- RequireEqual(1, sizeRead);
    var _ :- Require(!isDoneReading);

    var sRes :- reader.ReadBytes(0);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireEqual([], sRes);
    var _ :- RequireEqual(1, sizeRead);
    var _ :- Require(!isDoneReading);

    sRes :- reader.ReadBytes(3);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireEqual([3, 10, 20], sRes);
    var _ :- RequireEqual(4, sizeRead);
    var _ :- Require(!isDoneReading);

    var uint16 :- reader.ReadUInt16();
    var expectedUint16 := SeqToUInt16([50, 100]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireEqual(expectedUint16, uint16);
    var _ :- RequireEqual(6, sizeRead);
    var _ :- Require(!isDoneReading);

    var uint32 :- reader.ReadUInt32();
    var expectedUint32 := SeqToUInt32([150, 200, 250, 255]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireEqual(expectedUint32, uint32);
    var _ :- RequireEqual(10, sizeRead);
    var _ :- Require(isDoneReading);

    var isByteFailure := reader.ReadByte();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireFailure(isByteFailure);
    var _ :- RequireEqual(10, sizeRead);
    var _ :- Require(isDoneReading);

    var isBytesFailure := reader.ReadBytes(1);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireFailure(isBytesFailure);
    var _ :- RequireEqual(10, sizeRead);
    var _ :- Require(isDoneReading);

    var isUint16Failure := reader.ReadUInt16();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireFailure(isUint16Failure);
    var _ :- RequireEqual(10, sizeRead);
    var _ :- Require(isDoneReading);

    var isUint32Failure := reader.ReadUInt32();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- RequireFailure(isUint32Failure);
    var _ :- RequireEqual(10, sizeRead);
    r := Require(isDoneReading);
  }

  method {:test} TestSeqWriter() returns (r: Result<()>) {
    var writer := new Streams.SeqWriter<nat>();
    var _ :- RequireEqual([], writer.data);

    var elemSize := writer.WriteElements([]);
    var _ :- RequireEqual(0, elemSize);
    var _ :- RequireEqual([], writer.data);

    elemSize := writer.WriteElements([0, 100, 200]);
    var _ :- RequireEqual(3, elemSize);
    var _ :- RequireEqual([0, 100, 200], writer.data);

    elemSize := writer.WriteElements([300, 400, 500, 600]);
    var _ :- RequireEqual(4, elemSize);
    r := RequireEqual([0, 100, 200, 300, 400, 500, 600], writer.data);
  }

  method {:test} TestByteWriter() returns (r: Result<()>) {
    var writer := new Streams.ByteWriter();
    var dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([], dataWritten);
    var sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(0, sizeWritten);

    var res :- writer.WriteByte(0);
    var _ :- RequireEqual(1, res);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([0], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(1, sizeWritten);

    res :- writer.WriteBytes([]);
    var _ :- RequireEqual(0, res);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([0], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(1, sizeWritten);

    res :- writer.WriteBytes([5, 50, 100]);
    var _ :- RequireEqual(3, res);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([0, 5, 50, 100], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(4, sizeWritten);

    var uint16Written := SeqToUInt16([150, 200]);
    res :- writer.WriteUInt16(uint16Written);
    var _ :- RequireEqual(2, res);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([0, 5, 50, 100, 150, 200], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(6, sizeWritten);

    var uint32Written := SeqToUInt32([50, 150, 200, 255]);
    res :- writer.WriteUInt32(uint32Written);
    var _ :- RequireEqual(4, res);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([0, 5, 50, 100, 150, 200, 50, 150, 200, 255], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    r := RequireEqual(10, sizeWritten);
  }
}
