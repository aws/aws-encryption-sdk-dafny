
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/Collections.dfy"

module CollectionsTests {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Collections

  method {:test} ArrayByteProducer() {
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

  method ExpectNext(producer: ByteProducer, expected: uint8) 
    requires producer.Valid()
    ensures producer.Valid()
    modifies producer
  {
    expect producer.HasNext();
    var byte := producer.Next();
    expect byte == expected;
  }
}
