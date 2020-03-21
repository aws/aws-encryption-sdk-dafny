include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Consumers {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait ByteConsumer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    predicate method CanAccept() reads this, Repr
      requires Valid()
      ensures Valid()
    method Accept(b: uint8)
      requires Valid()
      requires CanAccept()
      ensures Valid()
      modifies this, Repr
      decreases Repr
  }

  trait {:extern} ExternalByteConsumer {
    ghost const Repr: set<object>
    predicate method CanAccept() reads this, Repr decreases Repr
    method Accept(b: uint8) modifies this, Repr decreases Repr
  }

  class AsExternalByteConsumer extends ExternalByteConsumer {
    const wrapped: ByteConsumer
    constructor(wrapped: ByteConsumer) {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr < Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    lemma {:axiom} AssumedValid() ensures Valid()
    predicate method CanAccept() reads this, Repr decreases Repr {
      AssumedValid();
      wrapped.CanAccept()
    }
    method Accept(b: uint8) modifies this, Repr decreases Repr {
      AssumedValid();
      expect CanAccept();
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
    method Accept(b: uint8) 
      requires Valid()
      ensures Valid()
      modifies this, Repr
      decreases Repr
    {
      wrapped.Accept(b);
    }
  }

  method ToExternalByteConsumer(c: ByteConsumer) returns (res: ExternalByteConsumer)
  {
    var result := Cast<AsByteConsumer>(c, _ => true);
    match result {
      case Some(adaptor) => 
        res := adaptor.wrapped; 
      case None =>
        res := new AsExternalByteConsumer(c);
    }
  }

  method FromExternalByteConsumer(c: ExternalByteConsumer) returns (res: ByteConsumer) 
    ensures res.Valid()
  {
    var result := Cast<AsExternalByteConsumer>(c, _ => true);
    match result {
      case Some(adaptor) =>
        adaptor.AssumedValid();
        res := adaptor.wrapped; 
      case None =>
        res := new AsByteConsumer(c);
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
      modifies Repr
      decreases Repr
    {
      bytes[index] := b;
      index := index + 1;
    }

    function method Capacity(): nat reads this requires Valid() {
      maxIndex - index
    }
  }
}