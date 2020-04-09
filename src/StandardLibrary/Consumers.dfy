include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./Validatable.dfy"

module {:extern} Consumers {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened ExternalInvariants

  trait ByteConsumer {
    ghost const Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases Repr
    predicate method CanAccept() reads Repr
      requires Valid()
      ensures Valid()
    method Accept(b: uint8)
      requires Valid()
      requires CanAccept()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
  }

  trait {:extern} ExternalByteConsumer {
    ghost const Repr: set<object>
    predicate Valid() 
      reads Repr
      decreases Repr
      ensures Valid() ==> this in Repr
    predicate method CanAccept() reads Repr decreases Repr
    method Accept(b: uint8) 
      modifies Repr 
      decreases Repr 
      ensures Valid()
      ensures Repr == old(Repr)
  }

  class AsExternalByteConsumer extends Validatable {
    const wrapped: ByteConsumer
    constructor(wrapped: ByteConsumer) 
      requires wrapped.Valid() 
      ensures Valid() 
      ensures this.Repr == {this, wrapped} + wrapped.Repr
    {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() 
      reads Repr 
      decreases Repr 
      ensures Valid() ==> this in Repr
    {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid() {

      }
    predicate method CanAccept() reads Repr decreases Repr {
      Axiom(Valid());
      wrapped.CanAccept()
    }
    method Accept(b: uint8) 
      modifies Repr 
      decreases Repr 
      ensures Valid()
      ensures Repr == old(Repr)
    {
      Axiom(Valid());
      expect CanAccept();
      wrapped.Accept(b);
    }
  }

  class AsByteConsumer extends ByteConsumer {
    const wrapped: ExternalByteConsumer
    constructor(wrapped: ExternalByteConsumer) requires wrapped.Valid()
      ensures Valid()
      ensures this.Repr == {this, wrapped} + wrapped.Repr
    {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    predicate Valid() reads Repr ensures Valid() ==> this in Repr decreases Repr {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    predicate method CanAccept() reads Repr
      requires Valid()
      ensures Valid()
      decreases Repr
    {
      wrapped.CanAccept()
    }
    method Accept(b: uint8) 
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr == old(Repr)
    {
      wrapped.Accept(b);
    }
  }

  method ToExternalByteConsumer(c: ByteConsumer) returns (res: ExternalByteConsumer)
    requires c.Valid()
    ensures res.Valid()
    ensures fresh(res.Repr - c.Repr)
  {
    var result := Cast<AsByteConsumer>(c, (casted: AsByteConsumer) => casted.Repr == c.Repr);
    match result {
      case Some(adaptor) =>
        Axiom(adaptor.Valid());
        res := adaptor.wrapped; 
      case None =>
        res := new AsExternalByteConsumer(c);
    }
  }

  method FromExternalByteConsumer(c: ExternalByteConsumer) returns (res: ByteConsumer) 
    requires c.Valid()
    ensures res.Valid()
    ensures fresh(res.Repr - c.Repr)
  {
    var result := Cast<AsExternalByteConsumer>(c, (casted: AsExternalByteConsumer) => casted.Repr == c.Repr);
    match result {
      case Some(adaptor) =>
        Axiom(adaptor.Valid());
        res := adaptor.wrapped;
      case None =>
        res := new AsByteConsumer(c);
    }
  }

  class ArrayWritingByteConsumer extends ByteConsumer {
    const bytes: array<uint8>
    var index: int
    var maxIndex: int
    predicate Valid() reads this decreases Repr {
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