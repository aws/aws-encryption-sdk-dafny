include "../../src/SDK/Serialize.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../Util/TestUtils.dfy"

module TestSerialize {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Serialize
  import UTF8
  import EncryptionContext
  import TestUtils

  method {:test} TestSerializeAAD() {
    var wr := new Streams.ByteWriter();
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);

    var expectedSerializedAAD := [0, 26, 0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];

    var len :- expect SerializeAAD(wr, encryptionContext);
    expect wr.GetDataWritten() == expectedSerializedAAD;
  }

  method {:test} TestSerializeAADEmpty() {
    reveal EncryptionContext.Serializable();
    var wr := new Streams.ByteWriter();
    var encryptionContext := map[];

    var expectedSerializedAAD := [0, 0];

    var len :- expect SerializeAAD(wr, encryptionContext);
    expect wr.GetDataWritten() == expectedSerializedAAD;
  }

  method {:test} TestSerializeLargeValidEC() {
    var wr := new Streams.ByteWriter();
    var encCtx := TestUtils.GenerateLargeValidEncryptionContext();

    var len :- expect SerializeAAD(wr, encCtx);
    expect len == 4 + |encCtx| as int * 7;
  }

  method {:test} TestSerializeKVPairs() {
    var wr := new Streams.ByteWriter();
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    TestUtils.ValidSmallEncryptionContext(encryptionContext);

    var expectedSerializedAAD := [0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];

    var len :- expect SerializeKVPairs(wr, encryptionContext);
    expect wr.GetDataWritten() == expectedSerializedAAD;
  }

  method {:test} TestSerializeKVPairsEmpty() {
    reveal EncryptionContext.Serializable();
    var wr := new Streams.ByteWriter();
    var encryptionContext := map[];

    var expectedSerializedAAD := [];

    var len :- expect SerializeKVPairs(wr, encryptionContext);
    expect wr.GetDataWritten() == expectedSerializedAAD;
  }
}
