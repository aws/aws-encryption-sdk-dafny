
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../StandardLibrary/Consumers.dfy"

module {:extern} Producers {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Consumers

  // TODO-RS: This should REALLY be Producer<T>, and similarly for all the
  // other interfaces defined here, but unfortunately Dafny
  // does not support type parameterization on traits.
  trait ByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    predicate method HasNext() reads Repr requires Valid() 
      
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))

    method Siphon(consumer: ByteConsumer) returns (siphoned: int)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      modifies Repr, consumer.Repr
      decreases *
      ensures Valid()
      ensures consumer.Valid()
      ensures Repr == old(Repr)
      ensures consumer.Repr == old(consumer.Repr)
  }

  trait {:extern} ExternalByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    predicate method HasNext() 
      requires Valid() // TODO-RS: unsound
      reads Repr
      decreases Repr
      ensures Valid()
    method Next() returns (res: uint8)
      requires Valid() // TODO-RS: unsound
      modifies Repr 
      decreases Repr
      ensures Valid() 
      ensures Repr == old(Repr)
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) 
      requires Valid() // TODO-RS: unsound
      requires consumer.Valid()
      requires Repr !! consumer.Repr  // TODO-RS: unsound
      modifies Repr, consumer.Repr
      decreases * 
      ensures Valid()
      ensures consumer.Valid()
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
      reads Repr 
      requires Valid() 
      ensures Valid() 
      decreases Repr 
    {
      wrapped.HasNext()
    }
    method Next() returns (res: uint8) 
      requires Valid()
      modifies Repr
      decreases Repr 
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      res := wrapped.Next();
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      modifies this, Repr, consumer, consumer.Repr
      decreases *
      ensures Valid()
      ensures consumer.Valid()
      ensures Repr == old(Repr)
      ensures consumer.Repr == old(consumer.Repr)
    {
      var externalConsumer := ToExternalByteConsumer(consumer);
      siphoned := wrapped.Siphon(externalConsumer);
      // TODO-RS: Not sure how to connect the external and internal versions yet
      Axiom(consumer.Valid());
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
      requires Valid() // TODO-RS: unsound
      reads Repr 
      ensures Valid()
    {
      wrapped.HasNext()
    }
    method Next() returns (res: uint8)
      requires Valid() // TODO-RS: unsound
      modifies Repr 
      decreases Repr 
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      expect HasNext();
      res := wrapped.Next();
    }
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) 
      requires Valid() // TODO-RS: unsound
      requires consumer.Valid()
      requires Repr !! consumer.Repr  // TODO-RS: unsound
      modifies Repr, consumer.Repr
      decreases * 
      ensures Valid()
      ensures consumer.Valid()
    {
      Axiom(Valid());
      Axiom(Repr !! consumer.Repr);

      var externalConsumer := FromExternalByteConsumer(consumer);
      siphoned := wrapped.Siphon(externalConsumer);
      // TODO-RS: Not sure how to connect the external and internal versions yet
      Axiom(consumer.Valid());
    }
  }

  method DefaultSiphon(producer: ByteProducer, consumer: ByteConsumer) returns (siphoned: int) 
    requires producer.Valid()
    requires consumer.Valid()
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
      ensures Valid()
    {
      index < maxIndex
    }
    method Next() returns (res: uint8) 
      requires Valid()
      requires HasNext()
      modifies this
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      res := bytes[index];
      index := index + 1;
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int) 
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      modifies this, Repr, consumer, consumer.Repr
      decreases *
      ensures Valid()
      ensures consumer.Valid()
    {
      var asArrayWriter := Cast<ArrayWritingByteConsumer>(consumer, (w: ArrayWritingByteConsumer) reads w, w.Repr => 
          (var o: object := w; o) == (var o: object := consumer; o));
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
    predicate method HasNext() reads this decreases Repr {
      |bytesRemaining| > 0
    }
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      modifies this
      decreases Repr
      ensures Valid()
    {
      res := bytesRemaining[0];
      bytesRemaining := bytesRemaining[1..];
    }
    method Siphon(consumer: ByteConsumer) returns (siphoned: int) 
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr
      modifies this, Repr, consumer, consumer.Repr
      decreases *
      ensures Valid()
      ensures consumer.Valid()
    {
      siphoned := DefaultSiphon(this, consumer);
    }
  }
}