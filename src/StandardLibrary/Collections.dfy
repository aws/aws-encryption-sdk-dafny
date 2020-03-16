
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Collections {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait {:termination false} ByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    predicate method HasNext() reads this, Repr
      requires Valid() 
      ensures Valid()
      
    method Next() returns (res: Result<uint8>) 
      requires Valid()
      requires HasNext()
      ensures Valid()
      modifies this

    method Siphon(consumer: ByteConsumer) returns (siphoned: Result<int>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr2
      // TODO-RS: These two should follow from the disjointness requirement
      // above and `Valid() ==> this in Repr`
      requires this !in consumer.Repr2
      requires consumer !in Repr
      ensures Valid()
      modifies this, Repr, consumer, consumer.Repr2
      decreases *
  }

  trait {:termination false} ByteConsumer {
    // TODO Something can't be both a consumer and a provider and both have a repr >:(
    ghost const Repr2: set<object>
    predicate Valid() reads this, Repr2
    predicate method CanAccept() reads this, Repr2
      requires Valid()
      ensures Valid()
    method Accept(b: uint8) returns (res: Result<()>)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr2
  }

  // Updating this to siphon one byte per call, in order to interface better with chunking for now
  // TODO: How do we want to approach this generally? Can we build off of this case? Or do we
  // need to update how we're handling this?
  // TODO how do we indicate end of stream?
  // TODO update to siphon up to count?
  method DefaultSiphon(producer: ByteProducer, consumer: ByteConsumer) returns (res: Result<int>) 
    requires producer.Valid()
    requires consumer.Valid()
    requires producer !in consumer.Repr2
    requires consumer !in producer.Repr
    requires producer.Repr !! consumer.Repr2
    ensures producer.Valid()
    ensures consumer.Valid()
    modifies producer, producer.Repr, consumer, consumer.Repr2
    decreases *
  {
    var siphoned := 0;
    if producer.HasNext() && consumer.CanAccept()
    {
      var byte :- producer.Next();
      var _ :- consumer.Accept(byte);
      siphoned := siphoned + 1;
      res := Success(siphoned);
      return res;
    }
    return Success(siphoned);
  }
/*
  class ArrayByteProducer extends ByteProducer {
    const bytes: array<uint8>
    var index: int
    var maxIndex: int
    predicate Valid() reads this ensures Valid() ==> this in Repr {
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
    method HasNext()
      requires Valid() 
      ensures Valid()      
    {
      b := index < maxIndex;
    }
    method Next() returns (res: Result<uint8>) 
      requires Valid()
      //requires HasNext()
      ensures Valid()
      modifies this
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
        // TODO-RS: Prove instead of dynamically checking
        expect 0 <= asArrayWriter.get.index < asArrayWriter.get.bytes.Length - siphoned;
        expect index + siphoned <= bytes.Length;
        UpdateRange(asArrayWriter.get.bytes, asArrayWriter.get.index, bytes[index..(index + siphoned)]);
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
    predicate Valid() reads this ensures Valid() ==> this in Repr {
      this in Repr
    }
    method HasNext() returns (b: bool)
      requires Valid() 
      ensures Valid()      
    {      
      b := |bytesRemaining| > 0;
    }
    method Next() returns (res: Result<uint8>) 
      requires Valid()
      requires HasNext()
      modifies this
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
      ensures fresh(Repr - {this, bytes})
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

    function method Capacity(): nat reads this requires Valid() {
      maxIndex - index
    }
  }
  */
}
