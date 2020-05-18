include "StandardLibrary.dfy"
include "UInt.dfy"
include "../Util/UTF8.dfy"

module {:extern "Collections"} Collections {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait {:termination false} Enumerator<T> {
    var signaledDone: bool
    var hasFailed: bool
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    method Next() returns (element: Result<Option<T>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone
  }

  trait {:termination false} Aggregator<T> {
    ghost var Repr: set<object>
    var done: bool
    var hasFailed: bool

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    method Accept(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      // TODO: Still not sure about allowing Success(false) here

    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> done
      // TODO: Still not sure about allowing Success(false) here
  }

  // SeqEnumerator implements an enumerator which enumerates one T from an underlying seq<T> at a time
  class SeqEnumerator<T> extends Enumerator<T> {
    const s: seq<T>
    ghost var enumerated: seq<T>
    var i: nat

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && i <= |s|
      && enumerated == s[..i]
      && this in Repr 
    }

    constructor (data: seq<T>)
      ensures s == data
      ensures enumerated == []
      ensures !signaledDone
      ensures !hasFailed
      ensures i == 0
      ensures Valid() && fresh(Repr)
    {
        s := data;
        enumerated := [];
        signaledDone := false;
        hasFailed := false;
        i := 0;
        Repr := {this};
    }
    
    method Next() returns (element: Result<Option<T>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone

      /* Postconditions specific to SeqChunkEnumerator */
      ensures !signaledDone && !hasFailed && old(i) < |s| ==>
        && i == old(i) + 1
        && element.Success?
        && element.value.Some?
        && element.value.get == s[old(i)]
      ensures !signaledDone && !hasFailed && old(i) == |s| ==>
        && i == |s|
        && element.Success?
        && element.value.None?
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Enumerator has ended and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      } else if i >= |s| {
        signaledDone := true;
        return Success(None());
      }

        
      var data := s[i];
      i := i + 1;
      enumerated := enumerated + [data];
      return Success(Some(data));
    }
  }

  // SeqChunkEnumerator implements an enumerator which enumerates a seq<T> up to size chunkSize from
  // an underlying seq<T>.
  class SeqChunkEnumerator<T> extends Enumerator<seq<T>> {
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

      /* Postconditions specific to SeqChunkEnumerator */
      ensures element.Success? && element.value.None? ==> i == |s|
      ensures
        var endSlice := Min(|s|, old(i)+chunkSize);
        element.Success? && element.value.Some? ==> element.value.get == s[old(i)..endSlice]
        && i == endSlice
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Enumerator has ended and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      } else if i >= |s| {
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

  // SeqAggregator implements an aggregator that accepts one T at a time to an underlying seq<T>
  class SeqAggregator<T> extends Aggregator<T> {
    var s: seq<T>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      this in Repr 
    }

    constructor ()
      ensures !done
      ensures !hasFailed
      ensures Valid() && fresh(Repr)
    {
        s := [];
        done := false;
        hasFailed := false;
        Repr := {this};
    }

    method Accept(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures !done && !hasFailed ==> res.Success? && res.value
    {
      if done {
        hasFailed := true;
        return Failure("Aggregator has been ended and cannot accept any more data");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      s := s + [element];
      return Success(true);
    }

    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> done
      ensures !done && !hasFailed ==> res.Success? && res.value
    {
      if done {
        hasFailed := true;
        return Failure("Aggregator is already Ended.");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      done := true;
      return Success(true);
    }
  }

  // SeqChunkAggregator implements an aggregator that concatenates input seq<T> on Accept to an
  // underlying seq<T>
  class SeqChunkAggregator<T> extends Aggregator<seq<T>> {
    var s: seq<T>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      this in Repr 
    }

    constructor ()
      ensures !done
      ensures !hasFailed
      ensures Valid() && fresh(Repr)
    {
        s := [];
        done := false;
        hasFailed := false;
        Repr := {this};
    }

    method Accept(element: seq<T>) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures !done && !hasFailed ==> res.Success? && res.value
    {
      if done {
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
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> done
      ensures !done && !hasFailed ==> res.Success? && res.value
    {
      if done {
        hasFailed := true;
        return Failure("Aggregator is already Ended.");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      done := true;
      return Success(true);
    }
  }
}
