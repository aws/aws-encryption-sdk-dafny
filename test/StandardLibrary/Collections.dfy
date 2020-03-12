
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
    expect producer.HasNext();
    var byte := producer.Next();
    expect byte == 1;
  }

  method ExpectNext(producer: ByteProducer, expected: uint8) 
    requires producer.Valid()
    ensures producer.Valid()
    modifies producer
  {
    expect producer.HasNext();
    var byte := producer.Next();
    expect byte == 1;
  }
}
