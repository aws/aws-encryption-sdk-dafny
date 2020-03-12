
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Collections {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait ByteProducer {
    var Repr: set<object>
    predicate Valid() reads this, Repr
    predicate method HasNext() reads this, Repr
      requires Valid() 
      ensures Valid()
      
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      ensures Valid()
      modifies this

    method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, consumer
      decreases *
  }

  trait ByteConsumer {
    var Repr: set<object>
    predicate Valid() reads this, Repr
    predicate method CanAccept() reads this, Repr
      requires Valid()
      ensures Valid()
    method Accept(b: uint8)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr
  }

  method DefaultTryForEachRemaining(producer: ByteProducer, consumer: ByteConsumer) returns (consumed: int) 
    requires producer.Valid()
    requires consumer.Valid()
    requires producer.Repr !! consumer.Repr
    ensures producer.Valid()
    ensures consumer.Valid()
    modifies producer, consumer
    decreases *
  {
    consumed := 0;
    while producer.HasNext() && consumer.CanAccept()
      invariant producer.Valid()
      invariant consumer.Valid()
      decreases * 
    {
      var byte := producer.Next();
      consumer.Accept(byte);
      consumed := consumed + 1;
    }
  }

  class ArrayByteProducer extends ByteProducer {
    const bytes: array<uint8>
    var index: int
    var maxIndex: int
    predicate Valid() reads this {
      0 <= index <= maxIndex <= bytes.Length
    }
    constructor(bytes: array<uint8>) 
      ensures Valid()
    {
      this.bytes := bytes;
      this.index := 0;
      this.maxIndex := bytes.Length;
    }
    predicate method HasNext() reads this requires Valid() ensures Valid() {
      index < maxIndex
    }
    method Next() returns (res: uint8) 
      requires Valid()
      requires HasNext()
      ensures Valid()
      modifies this
    {
      res := bytes[index];
      index := index + 1;
    }
    method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int) 
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, consumer
      decreases *
    {
      consumed := DefaultTryForEachRemaining(this, consumer);
    }
  }

  class SequenceByteProducer extends ByteProducer {
    var bytesRemaining: seq<uint8>
    predicate Valid() reads this {
      true
    }
    predicate method HasNext() reads this {
      |bytesRemaining| > 0
    }
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      modifies this
    {
      res := bytesRemaining[0];
      bytesRemaining := bytesRemaining[1..];
    }
    method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int) 
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, consumer
      decreases *
    {
      consumed := DefaultTryForEachRemaining(this, consumer);
    }
  }

  class ArrayWritingByteConsumer extends ByteConsumer {
    const bytes: array<uint8>
    var index: int
    var maxIndex: int
    predicate Valid() reads this {
      && 0 <= index <= maxIndex <= bytes.Length
      && Repr == {this, bytes}
    }
    constructor(bytes: array<uint8>) 
      ensures Valid()
    {
      this.bytes := bytes;
      this.index := 0;
      this.maxIndex := bytes.Length;
      this.Repr := {this, bytes};
    }
    predicate method CanAccept() reads this requires Valid() ensures Valid() {
      index < maxIndex
    }
    method Accept(b: uint8)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr
    {
      bytes[index] := b;
      index := index + 1;
    }
  }
}