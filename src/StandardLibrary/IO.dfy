include "StandardLibrary.dfy"
include "UInt.dfy"

module {:extern "IO"} IO {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait BytesEnumerator {
    var signaledEOF: bool
    var hasFailed: bool
    ghost const Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr

    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed // hasFailed can include an EOF error?
      ensures element.Success? && element.value.None? ==> signaledEOF // Cannot indicate EOF with data, has to be seperate call  }
  }

/*
  TODO
  trait Aggregator<T> {

    ghost const Repr: set<object> // const?

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr

    method Accept(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed // hasFailed can include an EOF error? 

    // TOOD: if T is not a seq, this means that you can only send one element as part of End
    method End(element: T) returns (res: Result<bool>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed // hasFailed can include an EOF error?
      ensures res.Success? && res.value ==> signaledEOF
  }
*/

  class ExternBytesEnumerator extends BytesEnumerator {
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    {
      && this in Repr 
    }

    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed // hasFailed can include an EOF error?
      ensures element.Success? && element.value.None? ==> signaledEOF // Cannot indicate EOF with data, has to be seperate call
    {
      if signaledEOF {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      }
      var externRes := NextExtern();
      if externRes.Failure? {
        hasFailed := true;
      } else if externRes.value.None? {
        signaledEOF := true;
      }
      return externRes;
    }

    method {:extern "NextExtern"} NextExtern() returns (element: Result<Option<seq<uint8>>>)
  }

  // TODO Move this
  // Wraps and operates on an ExternBytesEnumerator
  class EncryptEnumerator extends BytesEnumerator {
    var source: ExternBytesEnumerator
    var inBuffer: seq<uint8>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    {
      && this in Repr 
      && source in Repr && source.Repr <= Repr && this !in source.Repr
      && source.Valid()
    }

    constructor (source: ExternBytesEnumerator)
      requires source.Valid() 
      ensures this.source == source
      ensures !hasFailed
      ensures !signaledEOF
      ensures inBuffer == []
      ensures Valid() && fresh(Repr - source.Repr)
    {
      this.source := source;
      this.hasFailed := false;
      this.signaledEOF := false;
      this.inBuffer := [];
      this.Repr := {this} + source.Repr;
    }

    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed // hasFailed can include an EOF error?
      ensures element.Success? && element.value.None? ==> signaledEOF // Cannot indicate EOF with data, has to be seperate call
    {
      if signaledEOF {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      }

      // right now just pass through data

      // will never be true while we're passing through data
      if |inBuffer| < 0 {
        element := Success(Some(inBuffer));
        inBuffer := [];
        return element;
      }
      
      var res := source.Next();
      if res.Failure? {
        hasFailed := true;
        return res;
      } else if res.value.None? {
        signaledEOF := true;
        return res;
      }

      return res;
    }
  }

  // Native Enumerator implementation for enumerating bytes from a particular seq<uint8>
  // in a specified chunk size
  class BytesSeqEnumerator extends BytesEnumerator {
    const s: seq<uint8>
    const chunkSize: nat
    var i: nat

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr decreases this, Repr
    {
      && i <= |s|
      && chunkSize > 0
      && this in Repr 
    }

    constructor (data: seq<uint8>, chunkSize: nat)
      requires chunkSize > 0
      ensures s == data
      ensures !signaledEOF
      ensures !hasFailed
      ensures i == 0
      ensures this.chunkSize == chunkSize
      ensures Valid()
    {
        s := data;
        signaledEOF := false;
        hasFailed := false;
        i := 0;
        this.chunkSize := chunkSize;
        Repr := {this};
    }
    
    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies this, Repr
      decreases this, Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledEOF) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed // Should hasFailed include EOF error?
      ensures element.Success? && element.value.None? ==> signaledEOF // Cannot indicate EOF with data, has to be seperate call

      /* Postconditions specific to SeqEnumerator */
      ensures
        var endSlice := Min(|s|, old(i)+chunkSize);
        element.Success? && element.value.Some? ==> element.value.get == s[old(i)..endSlice]
        && i == endSlice
    {
      if signaledEOF {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      } else if i >= |s| {
        //EOF
        signaledEOF := true;
        return Success(None());
      }

        
      var endSlice := Min(|s|, i+chunkSize);
      var data := s[i..endSlice];
      i := endSlice;
      return Success(Some(data));
    }
  }
}
