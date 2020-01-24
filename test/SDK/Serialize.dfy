include "../../src/SDK/Serialize.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestSerialize {
  import opened StandardLibrary
  import opened Serialize
  import UTF8
  import MessageHeader

  method {:test} TestSerializeAADHappy() returns (ret: Result<()>) {
    var wr := new Streams.StringWriter();
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    MessageHeader.AssumeValidAAD(encryptionContext);

    var expectedSerializedAAD := [0, 14, 0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.data, expectedSerializedAAD);
  }

  method {:test} TestSerializeAADEmpty() returns (ret: Result<()>) {
    reveal MessageHeader.ValidAAD();
    var wr := new Streams.StringWriter();
    var encryptionContext := [];

    var expectedSerializedAAD := [0, 0];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.data, expectedSerializedAAD);
  }
}
