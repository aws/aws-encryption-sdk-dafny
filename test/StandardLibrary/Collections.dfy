
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/Producers.dfy"

module TestCollection {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Producers
  import opened Consumers

  method {:test} ArrayByteProducerNext() {
    var bytes := new uint8[5];
    bytes[0] := 1;
    bytes[1] := 2;
    bytes[2] := 3;
    bytes[3] := 4;
    bytes[4] := 5;

    var producer := new ArrayByteProducer(bytes);
    ExpectNext(producer, 1);
    ExpectNext(producer, 2);
    ExpectNext(producer, 3);
    ExpectNext(producer, 4);
    ExpectNext(producer, 5);
    expect !producer.HasNext();
  }

  method {:test} ArrayByteProducerSiphonToArrayWithCapacity() decreases * {
    var bytes := new uint8[5];
    bytes[0] := 1;
    bytes[1] := 2;
    bytes[2] := 3;
    bytes[3] := 4;
    bytes[4] := 5;
    var bytesOut := new uint8[10];

    var producer := new ArrayByteProducer(bytes);
    var consumer := new ArrayWritingByteConsumer(bytesOut);
    var siphoned := producer.Siphon(consumer);
    expect siphoned == 5;
    expect bytesOut[..] == [1, 2, 3, 4, 5, 0, 0, 0, 0, 0];
  }

  method {:test} ArrayByteProducerSiphonToArrayWithoutCapacity() decreases * {
    var bytes := new uint8[5];
    bytes[0] := 1;
    bytes[1] := 2;
    bytes[2] := 3;
    bytes[3] := 4;
    bytes[4] := 5;
    var bytesOut := new uint8[3];

    var producer := new ArrayByteProducer(bytes);
    var consumer := new ArrayWritingByteConsumer(bytesOut);
    var siphoned := producer.Siphon(consumer);
    expect siphoned == 3;
    expect bytesOut[..] == [1, 2, 3];
  }

  method ExpectNext(producer: ByteProducer, expected: uint8) 
    requires producer.Valid()
    ensures producer.Valid()
    modifies producer, producer.Repr
  {
    expect producer.HasNext();
    var byte := producer.Next();
    expect byte == expected;
  }
}
