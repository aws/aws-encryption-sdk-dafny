include "../../src/SDK/Serialize.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestSerialize {
  import opened StandardLibrary
  import opened Serialize
  import UTF8
  import MessageHeader

  method {:test} TestSerializeAAD() returns (ret: TestResult) {
    var wr := new Streams.ByteWriter();
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    MessageHeader.AssumeValidAAD(encryptionContext);

    var expectedSerializedAAD := [0, 14, 0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeAADEmpty() returns (ret: TestResult) {
    reveal MessageHeader.ValidAAD();
    var wr := new Streams.ByteWriter();
    var encryptionContext := [];

    var expectedSerializedAAD := [0, 0];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeKVPairs() returns (ret: TestResult) {
    var wr := new Streams.ByteWriter();
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    MessageHeader.AssumeValidAAD(encryptionContext);

    var expectedSerializedAAD := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
  
    var len :- SerializeKVPairs(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeKVPairsEmpty() returns (ret: TestResult) {
    reveal MessageHeader.ValidAAD();
    var wr := new Streams.ByteWriter();
    var encryptionContext := [];

    var expectedSerializedAAD := [];
  
    var len :- SerializeKVPairs(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }
}
