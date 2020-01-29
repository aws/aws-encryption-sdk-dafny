include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Streams.dfy"

module TestStreams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Streams

  method {:test} TestSeqReaderReadElements() returns (r: Result<()>) {
    var s: seq<nat> := [100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res := reader.ReadElements(3);
    var _ :- RequireEqual([100, 200, 300], res);

    res := reader.ReadElements(0);
    var _ :- RequireEqual([], res);

    res := reader.ReadElements(1);
    r := RequireEqual([400], res);
  }

  method {:test} TestSeqReaderReadExact() returns (r: Result<()>) {
    var s: seq<nat> := [100, 200, 300, 400];
    var reader := new Streams.SeqReader<nat>(s);

    var res := reader.ReadExact(3);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual([100, 200, 300], res.value);

    res := reader.ReadExact(0);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual([], res.value);

    res := reader.ReadExact(1);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual([400], res.value);

    res := reader.ReadExact(1);
    r := Require(res.Failure?);
  }

  method {:test} TestByteReader() returns (r: Result<()>) {
    var s: seq<uint8> := [3, 10, 20, 50, 100, 150, 200, 250, 255];
    var reader := new Streams.ByteReader(s);

    var uint8Res := reader.ReadByte();
    var sizeRead := reader.GetSizeRead();
    var isDoneReading := reader.IsDoneReading();
    var _ :- Require(uint8Res.Success?);
    var _ :- RequireEqual(3, uint8Res.value);
    var _ :- RequireEqual(1, sizeRead);
    var _ :- Require(!isDoneReading);

    var sRes := reader.ReadBytes(0);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- Require(sRes.Success?);
    var _ :- RequireEqual([], sRes.value);
    var _ :- RequireEqual(1, sizeRead);
    var _ :- Require(!isDoneReading);

    sRes := reader.ReadBytes(2);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- Require(sRes.Success?);
    var _ :- RequireEqual([10, 20], sRes.value);
    var _ :- RequireEqual(3, sizeRead);
    var _ :- Require(!isDoneReading);

    var uint16 := reader.ReadUInt16();
    var expectedUint16 := SeqToUInt16([50, 100]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- Require(uint16.Success?);
    var _ :- RequireEqual(expectedUint16, uint16.value);
    var _ :- RequireEqual(5, sizeRead);
    var _ :- Require(!isDoneReading);

    var uint32 := reader.ReadUInt32();
    var expectedUint32 := SeqToUInt32([150, 200, 250, 255]);
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- Require(uint32.Success?);
    var _ :- RequireEqual(expectedUint32, uint32.value);
    var _ :- RequireEqual(9, sizeRead);
    var _ :- Require(isDoneReading);

    uint8Res := reader.ReadByte();
    sizeRead := reader.GetSizeRead();
    isDoneReading := reader.IsDoneReading();
    var _ :- Require(uint8Res.Failure?);
    var _ :- RequireEqual(9, sizeRead);
    r := Require(isDoneReading);
  }

  method {:test} TestSeqWriter() returns (r: Result<()>) {
    var writer := new Streams.SeqWriter<nat>();
    var _ :- RequireEqual([], writer.data);

    var elemSize := writer.WriteElements([]);
    var _ :- RequireEqual(0, elemSize);
    var _ :- RequireEqual([], writer.data);

    elemSize := writer.WriteElements([100, 200]);
    var _ :- RequireEqual(2, elemSize);
    var _ :- RequireEqual([100, 200], writer.data);

    elemSize := writer.WriteElements([300, 400, 500]);
    var _ :- RequireEqual(3, elemSize);
    r := RequireEqual([100, 200, 300, 400, 500], writer.data);
  }

  method {:test} TestByteWriter() returns (r: Result<()>) {
    var writer := new Streams.ByteWriter();
    var dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([], dataWritten);
    var sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(0, sizeWritten);

    var res := writer.WriteByte(5);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual(1, res.value);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([5], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(1, sizeWritten);

    res := writer.WriteBytes([]);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual(0, res.value);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([5], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(1, sizeWritten);

    res := writer.WriteBytes([50, 100]);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual(2, res.value);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([5, 50, 100], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(3, sizeWritten);

    var uint16Written := SeqToUInt16([150, 200]);
    res := writer.WriteUInt16(uint16Written);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual(2, res.value);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([5, 50, 100, 150, 200], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    var _ :- RequireEqual(5, sizeWritten);

    var uint32Written := SeqToUInt32([50, 150, 200, 255]);
    res := writer.WriteUInt32(uint32Written);
    var _ :- Require(res.Success?);
    var _ :- RequireEqual(4, res.value);
    dataWritten := writer.GetDataWritten();
    var _ :- RequireEqual([5, 50, 100, 150, 200, 50, 150, 200, 255], dataWritten);
    sizeWritten := writer.GetSizeWritten();
    r := RequireEqual(9, sizeWritten);
  }
}
