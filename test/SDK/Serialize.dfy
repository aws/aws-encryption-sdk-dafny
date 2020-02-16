include "../../src/SDK/Serialize.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../Util/TestUtils.dfy"

module TestSerialize {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Serialize
  import UTF8
  import MessageHeader
  import TestUtils

  method {:test} TestSerializeAAD() returns (ret: Result<()>) {
    var wr := new Streams.ByteWriter();
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    MessageHeader.AssumeValidAAD(encryptionContext);

    var expectedSerializedAAD := [0, 26, 0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeAADEmpty() returns (ret: Result<()>) {
    reveal MessageHeader.ValidAAD();
    var wr := new Streams.ByteWriter();
    var encryptionContext := map[];

    var expectedSerializedAAD := [0, 0];
  
    var len :- SerializeAAD(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeLargeValidEC() returns (r: Result<()>) {   
    var wr := new Streams.ByteWriter();
    var encCtx :- TestUtils.GenerateLargeValidEncryptionContext();
    MessageHeader.AssumeValidAAD(encCtx);

    var len :- SerializeAAD(wr, encCtx);
    r := RequireEqual(len, 4 + |encCtx| as int * 7);
  }

  method {:test} TestSerializeKVPairs() returns (ret: Result<()>) {
    var wr := new Streams.ByteWriter();
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    MessageHeader.AssumeValidAAD(encryptionContext);

    var expectedSerializedAAD := [0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];
  
    var len :- SerializeKVPairs(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }

  method {:test} TestSerializeKVPairsEmpty() returns (ret: Result<()>) {
    reveal MessageHeader.ValidAAD();
    var wr := new Streams.ByteWriter();
    var encryptionContext := map[];

    var expectedSerializedAAD := [];
  
    var len :- SerializeKVPairs(wr, encryptionContext);
    ret := RequireEqual(wr.GetDataWritten(), expectedSerializedAAD);
  }
}
