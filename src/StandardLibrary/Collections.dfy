include "StandardLibrary.dfy"
include "UInt.dfy"
include "../Util/UTF8.dfy"

module {:extern "Collections"} Collections {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait {:termination false} Enumerator<T> {
    var signaledDone: bool
    var hasFailed: bool
    ghost const Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    method Next() returns (element: Result<Option<T>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone
      // TODO If T is a seq, then whether it's interpreted as an element
      // in some list of seq, or a chunk of a larger seq, depends on the
      // implementation. There is a problem, however, where the latter
      // is able to represent [] to mean "no data right now", while
      // the former has no such mechanism. This feels like this interface
      // half allows "no data right now", which seems bad.
  }

  trait {:termination false} Aggregator<T> {
    ghost const Repr: set<object>
    var signaledDone: bool
    var hasFailed: bool

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    method Accept(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      // TODO: Still not sure about allowing Success(false) here

    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> signaledDone
      // TODO: Still not sure about allowing Success(false) here
  }

  // Native Enumerator implementation for enumerating bytes from a particular seq<T>
  // in a specified chunk size
  class SeqEnumerator<T> extends Enumerator<seq<T>> {
    const s: seq<T>
    ghost var enumerated: seq<T>
    const chunkSize: nat
    var i: nat

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && i <= |s|
      && chunkSize > 0
      && enumerated == s[..i]
      && this in Repr 
    }

    constructor (data: seq<T>, chunkSize: nat)
      requires chunkSize > 0
      ensures s == data
      ensures enumerated == []
      ensures !signaledDone
      ensures !hasFailed
      ensures i == 0
      ensures this.chunkSize == chunkSize
      ensures Valid() && fresh(Repr)
    {
        s := data;
        enumerated := [];
        signaledDone := false;
        hasFailed := false;
        i := 0;
        this.chunkSize := chunkSize;
        Repr := {this};
    }
    
    method Next() returns (element: Result<Option<seq<T>>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone

      /* Postconditions specific to SeqEnumerator */
      ensures element.Success? && element.value.None? ==> i == |s|
      ensures
        var endSlice := Min(|s|, old(i)+chunkSize);
        element.Success? && element.value.Some? ==> element.value.get == s[old(i)..endSlice]
        && i == endSlice
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      } else if i >= |s| {
        //EOF
        signaledDone := true;
        return Success(None());
      }

        
      var endSlice := Min(|s|, i+chunkSize);
      var data := s[i..endSlice];
      i := endSlice;
      enumerated := enumerated + data;
      return Success(Some(data));
    }
  }

  // Native Enumerator implementation for enumerating bytes from a particular seq<T>
  // in a specified chunk size
  class SeqAggregator<T> extends Aggregator<seq<T>> {
    var s: seq<T>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      this in Repr 
    }

    constructor ()
      ensures !signaledDone
      ensures !hasFailed
      ensures Valid() && fresh(Repr)
    {
        s := [];
        signaledDone := false;
        hasFailed := false;
        Repr := {this};
    }

    method Accept(element: seq<T>) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Aggregator has been ended and cannot accept any more data");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      s := s + element;
      return Success(true);
    }

    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> signaledDone
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Aggregator is already at EOF");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      signaledDone := true;
      return Success(true);
    }
  }
}
