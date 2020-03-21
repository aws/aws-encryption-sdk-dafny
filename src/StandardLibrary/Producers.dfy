
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../StandardLibrary/Consumers.dfy"

module Producers {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Consumers

  // TODO-RS: This should REALLY be Producer<T>, and similarly for all the
  // other interfaces defined here, but unfortunately Dafny
  // does not support type parameterization on traits.
  trait ByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    predicate method HasNext() reads this, Repr
      requires Valid() 
      ensures Valid()
      decreases this, Repr
      
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)

    method Siphon(consumer: ByteConsumer) returns (siphoned: int)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      // TODO-RS: These two should follow from the disjointness requirement
      // above and `Valid() ==> this in Repr`
      requires this !in consumer.Repr
      requires consumer !in Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
  }

  trait {:extern} ExternalByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    predicate method HasNext() 
      reads this, Repr
      decreases this, Repr
      ensures Valid()
    method Next() returns (res: uint8)
      modifies this, Repr 
      decreases this, Repr
      ensures Valid() 
      ensures Repr == old(Repr)
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) 
      ensures Valid()
      modifies this, Repr 
      decreases *
  }

  class AsByteProducer extends ByteProducer {
    const wrapped: ExternalByteProducer
    constructor(wrapped: ExternalByteProducer) {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    predicate method HasNext() 
      reads this, Repr 
      requires Valid() 
      ensures Valid() 
      decreases this, Repr 
    {
      wrapped.HasNext()
    }
    method Next() returns (res: uint8) 
      requires Valid()
      modifies this, Repr
      decreases this, Repr 
      ensures Valid()
      ensures Repr == old(Repr)
    {
      res := wrapped.Next();
      assert wrapped.Valid();
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      // TODO-RS: These two should follow from the disjointness requirement
      // above and `Valid() ==> this in Repr`
      requires this !in consumer.Repr
      requires consumer !in Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      var externalConsumer := ToExternalByteConsumer(consumer);
      siphoned := wrapped.Siphon(externalConsumer);
    }
  }

  class AsExternalByteProducer extends ExternalByteProducer {
    const wrapped: ByteProducer
    constructor(wrapped: ByteProducer) {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    
    predicate method HasNext() 
      reads this, Repr 
      decreases this, Repr
      ensures Valid()
    {
      Axiom(Valid());
      wrapped.HasNext()
    }
    method Next() returns (res: uint8)
      modifies this, Repr 
      decreases this, Repr 
      ensures Valid()
      ensures Repr == old(Repr)
    {
      Axiom(Valid());
      expect HasNext();
      res := wrapped.Next();
    }
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) 
      modifies this, Repr, consumer, consumer.Repr
      decreases * 
      ensures Valid()
    {
      Axiom(Valid());
      var externalConsumer := FromExternalByteConsumer(consumer);
      siphoned := wrapped.Siphon(externalConsumer);
    }
  }

  method DefaultSiphon(producer: ByteProducer, consumer: ByteConsumer) returns (siphoned: int) 
    requires producer.Valid()
    requires consumer.Valid()
    requires producer !in consumer.Repr
    requires consumer !in producer.Repr
    requires producer.Repr !! consumer.Repr
    ensures producer.Valid()
    ensures consumer.Valid()
    modifies producer, producer.Repr, consumer, consumer.Repr
    decreases *
  {
    siphoned := 0;
    while producer.HasNext() && consumer.CanAccept()
      invariant producer.Valid()
      invariant consumer.Valid()
      decreases * 
    {
      var byte := producer.Next();
      consumer.Accept(byte);
      siphoned := siphoned + 1;
    }
  }

  class ArrayByteProducer extends ByteProducer {
    const bytes: array<uint8>
    var index: int
    var maxIndex: int
    predicate Valid() reads this ensures Valid() ==> this in Repr decreases this, Repr {
      && 0 <= index <= maxIndex <= bytes.Length
      && this in Repr
    }
    constructor(bytes: array<uint8>) 
      ensures Valid()
      ensures fresh(Repr - {this, bytes})
    {
      this.bytes := bytes;
      this.index := 0;
      this.maxIndex := bytes.Length;
      this.Repr := {this, bytes};
    }
    predicate method HasNext() 
      requires Valid()
      reads this
      decreases this, Repr
      ensures Valid()
    {
      index < maxIndex
    }
    method Next() returns (res: uint8) 
      requires Valid()
      requires HasNext()
      modifies this
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
    {
      res := bytes[index];
      index := index + 1;
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int) 
      requires Valid()
      requires consumer.Valid()
      requires this !in consumer.Repr
      requires consumer !in Repr
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      var asArrayWriter := Cast<ArrayWritingByteConsumer>(consumer, (w: ArrayWritingByteConsumer) reads w, w.Repr => 
          w.Valid() && w.Repr == consumer.Repr);
      if asArrayWriter.Some? {
        siphoned := Min(Remaining(), asArrayWriter.get.Capacity());
        UpdateRange(asArrayWriter.get.bytes, asArrayWriter.get.index, bytes[index..(index + siphoned)]);
        asArrayWriter.get.index := asArrayWriter.get.index + siphoned;
        index := index + siphoned;
      } else {
        siphoned := DefaultSiphon(this, consumer);
      }
    }
    function method Remaining(): nat reads this requires Valid() {
      maxIndex - index
    }
  }

  class SequenceByteProducer extends ByteProducer {
    var bytesRemaining: seq<uint8>
    predicate Valid() reads this ensures Valid() ==> this in Repr decreases this, Repr {
      this in Repr
    }
    predicate method HasNext() reads this decreases this, Repr {
      |bytesRemaining| > 0
    }
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      modifies this
      decreases this, Repr
      ensures Valid()
    {
      res := bytesRemaining[0];
      bytesRemaining := bytesRemaining[1..];
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int) 
      requires Valid()
      requires consumer.Valid()
      requires this !in consumer.Repr
      requires consumer !in Repr
      requires Repr !! consumer.Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr
      decreases *
    {
      siphoned := DefaultSiphon(this, consumer);
    }
  }
}