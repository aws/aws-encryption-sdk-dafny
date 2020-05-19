include "StandardLibrary.dfy"

module {:extern "Collections"} Collections {
  import opened StandardLibrary

  // Enumerator is an interface for enumerating finite elements of type T
  trait {:termination false} Enumerator<T> {
    var signaledDone: bool
    var hasFailed: bool
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    // Next returns the next element T in the enumeration, Success(None) to
    // indicate the end of elements, or a Failure.
    // If calling after the end of elements has already been indicated,
    // returns a Failure.
    // If a Failure has been returned, the enumerator goes into a failed state
    // and will always return a Failure on Next()
    method Next() returns (element: Result<Option<T>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone
  }

  // Aggregator is an interface for aggregating finite elements of type T
  trait {:termination false} Aggregator<T> {
    ghost var Repr: set<object>
    var done: bool
    var hasFailed: bool

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    // Accept puts the input element T into the aggregation and returns Success(true),
    // does not put the input element T into the aggregation and returns Success(false),
    // or returns a Failure.
    // If a Sucess(false) is returned, Accept() or End() are allowed to be called again.
    // If a Failure has been returned, the aggregator goes into a failed state
    // and will always return a Failure on Next()
    method Accept(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed

    // End signals the end of the aggregation and returns Success(true),
    // does not signal the end of the aggregation and returns Success(false),
    // or returns a Failure.
    // If a Sucess(false) is returned, Accept() or End() are allowed to be called again.
    // If a Failure has been returned, the aggregator goes into a failed state
    // and will always return a Failure on Next()
    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> done
  }

  // SeqEnumerator implements an enumerator which enumerates one T at a time from an underlying seq<T>
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

  // SeqChunkEnumerator implements an enumerator which enumerates an underlying seq<T>
  // in chunks of seq<T> of up to size chunkSize
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

  // SeqChunkAggregator implements an aggregator that concatenates chunks of seq<T>
  // to an underlying seq<T>
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
