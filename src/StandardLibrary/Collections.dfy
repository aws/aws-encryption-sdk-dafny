
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

import opened StandardLibrary
import opened UInt = StandardLibrary.UInt

trait ByteProducer {
  predicate Valid() reads this
  predicate method HasNext()
    requires Valid() 
    ensures Valid()
    reads this
  method Next() returns (res: Option<uint8>)
    requires Valid()
    ensures Valid()
    ensures HasNext() ==> res.Some? 
    modifies this

  method ForEachRemaining(consumer: ByteConsumer)
    requires Valid()
    ensures Valid()
    modifies this, consumer
    decreases *
  method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int)
    requires Valid()
    ensures Valid()
    modifies this, consumer
    decreases *
}

trait ByteConsumer {
  predicate method CanAccept()
  method Accept(b: uint8) returns (res: bool)
}

method DefaultForEachRemaining(producer: ByteProducer, consumer: ByteConsumer)
  requires producer.Valid()
  ensures producer.Valid()
  modifies producer, consumer
  decreases *
{
  while producer.HasNext() 
    invariant producer.Valid()
    decreases * 
  {
    var byte := producer.Next();
    // TODO-RS: Dafny isn't convinced this is always true for some reason
    if byte.Some? {
      var _ := consumer.Accept(byte.get);
    }
  }
}

method DefaultTryForEachRemaining(producer: ByteProducer, consumer: ByteConsumer) returns (consumed: int) 
  requires producer.Valid()
  ensures producer.Valid()
  modifies producer, consumer
  decreases *
{
  consumed := 0;
  while producer.HasNext() && consumer.CanAccept()
    invariant producer.Valid()
    decreases * 
  {
    var byte := producer.Next();
    // TODO-RS: Dafny isn't convinced this is always true for some reason
    if byte.Some? {
      var _ := consumer.Accept(byte.get);
    }
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
  predicate method HasNext() reads this requires Valid() ensures Valid() {
    index < maxIndex
  }
  method Next() returns (res: Option<uint8>) 
    requires Valid()
    ensures Valid()
    ensures HasNext() ==> res.Some? 
    modifies this
  {
    if index >= maxIndex {
      res := None;
    } else {
      res := Some(bytes[index]);
      index := index + 1;
    }
  }
  method ForEachRemaining(consumer: ByteConsumer) 
    requires Valid()
    ensures Valid()
    modifies this, consumer
    decreases *
  {
    DefaultForEachRemaining(this, consumer);
  }
  method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int) 
    requires Valid()
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
  method Next() returns (res: Option<uint8>)
    requires Valid()
    ensures Valid()
    ensures HasNext() ==> res.Some? 
    modifies this
  {
    if |bytesRemaining| == 0 {
      res := None;
    } else {
      res := Some(bytesRemaining[0]);
      bytesRemaining := bytesRemaining[1..];
    }
  }
  method ForEachRemaining(consumer: ByteConsumer) 
    requires Valid()
    ensures Valid()
    modifies this, consumer
    decreases *
  {
    DefaultForEachRemaining(this, consumer);
  }
  method TryForEachRemaining(consumer: ByteConsumer) returns (consumed: int) 
    requires Valid()
    ensures Valid()
    modifies this, consumer
    decreases *
  {
    consumed := DefaultTryForEachRemaining(this, consumer);
  }
}