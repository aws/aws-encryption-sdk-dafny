
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Collections {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // TODO-RS: This should REALLY be Producer<T>, and similarly for all the
  // other interfaces defined here, but unfortunately Dafny
  // does not support type parameterization on traits.
  trait ByteProducer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    predicate method HasNext() reads this, Repr
      requires Valid() 
      ensures Valid()
      
    method Next() returns (res: uint8)
      requires Valid()
      requires HasNext()
      ensures Valid()
      modifies this, Repr

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

  type ValidByteProducer? = p: ByteProducer? | p == null || p.Valid()

  trait {:extern} ExternalByteProducer {
    ghost const Repr: set<object>
    predicate method HasNext() reads this, Repr decreases Repr
    method Next() returns (res: uint8) modifies this, Repr decreases Repr
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) decreases *
  }

  class AsByteProducer extends ByteProducer {
    const wrapped: ExternalByteProducer
    constructor(wrapped: ExternalByteProducer) {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
        && this in Repr 
        && wrapped in Repr 
        && wrapped.Repr < Repr 
        && this !in wrapped.Repr
    }
    predicate method HasNext() 
      reads this, Repr 
      requires Valid() 
      ensures Valid() 
      decreases Repr 
    {
      wrapped.HasNext()
    }
    method Next() returns (res: uint8) 
      requires Valid()
      ensures Valid()
      modifies this, Repr
      decreases Repr 
    {
      res := wrapped.Next();
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
    const wrapped: ValidByteProducer?
    constructor(wrapped: ValidByteProducer?) requires wrapped != null {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate method HasNext() 
      reads this, Repr 
      decreases Repr
    {
      if wrapped != null then wrapped.HasNext() else false
    }
    method Next() returns (res: uint8) modifies this, Repr decreases Repr {
      expect wrapped != null;
      res := wrapped.Next();
    }
    method Siphon(consumer: ExternalByteConsumer) returns (siphoned: int) decreases * {
      var externalConsumer := FromExternalByteConsumer(consumer);
      expect wrapped != null;
      siphoned := wrapped.Siphon(externalConsumer);
    }
  }

  trait ByteConsumer {
    ghost const Repr: set<object>
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

  type ValidByteConsumer? = c: ByteConsumer? | c == null || c.Valid()

  trait {:extern} ExternalByteConsumer {
    ghost const Repr: set<object>
    predicate method CanAccept() reads this, Repr
    method Accept(b: uint8) modifies this, Repr
  }

  class AsExternalByteConsumer extends ExternalByteConsumer {
    const wrapped: ValidByteConsumer?
    constructor(wrapped: ValidByteConsumer?) requires wrapped != null {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate method CanAccept() reads this, Repr {
      if wrapped != null then wrapped.CanAccept() else false
    }
    method Accept(b: uint8) modifies this, Repr {
      expect wrapped != null;
      wrapped.Accept(b);
    }
  }

  class AsByteConsumer extends ByteConsumer {
    const wrapped: ExternalByteConsumer
    constructor(wrapped: ExternalByteConsumer) ensures Valid() {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr < Repr 
      && this !in wrapped.Repr
    }
    predicate method CanAccept() reads this, Repr
      requires Valid()
      ensures Valid()
      decreases Repr
    {
      wrapped.CanAccept()
    }
    method Accept(b: uint8) {
      wrapped.Accept(b);
    }
  }

  method ToExternalByteConsumer(c: ValidByteConsumer?) returns (res: ExternalByteConsumer?)
    ensures c != null <==> res != null
  {
    if c == null {
      res := null;
    } else {
      var result := Cast<AsByteConsumer>(c, _ => true);
      match result {
        case Some(adaptor) => 
          res := adaptor.wrapped; 
        case None =>
          res := new AsExternalByteConsumer(c);
      }
    }
  }

  method FromExternalByteConsumer(c: ExternalByteConsumer?) returns (res: ValidByteConsumer?) 
    ensures c != null <==> res != null
  {
    if c == null {
      res := null;
    } else {
      var result := Cast<AsExternalByteConsumer>(c, _ => true);
      match result {
        case Some(adaptor) =>
          expect adaptor.wrapped != null;
          res := adaptor.wrapped; 
        case None =>
          res := new AsByteConsumer(c);
      }
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
    predicate Valid() reads this ensures Valid() ==> this in Repr {
      this in Repr
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
}