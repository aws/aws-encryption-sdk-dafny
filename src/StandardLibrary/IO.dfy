include "StandardLibrary.dfy"
include "UInt.dfy"
include "Collections.dfy"

// Provides extern hookins for reading bytes from and writing bytes to
// operating system constructs such as files, TCP/IP sockets, and stdin/stdout.
module {:extern "IO"} IO {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Collections

  // ExternBytesEnumerator provides a Dafny Enumerator interface hooked up
  // to a extern implementation of a blocking read to some native source.
  class ExternBytesEnumerator extends Collections.Enumerator<seq<uint8>> {
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && this in Repr 
    }

    // Next reads sequential bytes from this Enumerator's native source.
    // This call blocks until at least one byte of data is read,
    // Success(None) (signalling Done) is returned, or a Failure is returned.
    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone 
      /* ExternBytesEnumerator class specification */
      // All successful Nexts on this Enuemrator that don't signal Done
      // must return some bytes.
      ensures element.Success? && element.value.Some? ==> |element.value.get| > 0
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      }
      var externRes := NextExtern();
      if externRes.Failure? {
        hasFailed := true;
      } else if externRes.value.None? {
        signaledDone := true;
      } else if |externRes.value.get| <= 0 {
        hasFailed := true;
        return Failure("Extern Next() implementation violated API contract.");
      }
      return externRes;
    }

    method {:extern "NextExtern"} NextExtern() returns (element: Result<Option<seq<uint8>>>)
  }

  // ExternBytesAggregator provides a Dafny Aggregator interface hooked up
  // to a extern implementation of a blocking write to some native sink.
  class ExternBytesAggregator extends Collections.Aggregator<seq<uint8>> {
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && this in Repr 
    }

    // Accept writes bytes sequentially to this Aggregator's native sink.
    // This call blocks until all input bytes are considered processed, or a Failure is returned.
    method Accept(element: seq<uint8>) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? ==> res.value
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Aggregator is at EOF and cannot be written to.");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }
      var externRes := AcceptExtern(element);
      if externRes.Failure? {
        hasFailed := true;
        return Failure("Aggregator native sink failed to Accept bytes.");
      } else if !externRes.value {
        hasFailed := true;
        return Failure("Extern implementation of Accept violated API contract.");
      }
      return externRes;
    }

    // End signals to this Aggregator's native sink the end of sequential byte input, and finishes
    // writing all remaining inputted bytes to the native sink.
    // This call blocks until all user inputted bytes are written to the native sink,
    // or a Failure is returned.
    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? ==> res.value && signaledDone

    {
      if signaledDone {
        hasFailed := true;
        return Failure("Aggregator is already at EOF");
      } else if hasFailed {
        return Failure("Aggregator is in a failed state.");
      }

      var externRes := EndExtern();
      if externRes.Failure? {
        hasFailed := true;
        return Failure("Aggregator native sink failed to End.");
      } else if !externRes.value {
        hasFailed := true;
        return Failure("Extern End() implementation violated API contract");
      }
      signaledDone := true;
      return externRes;
    }

    method {:extern "AcceptExtern"} AcceptExtern(element: seq<uint8>) returns (res: Result<bool>)
    method {:extern "EndExtern"} EndExtern() returns (res: Result<bool>)
  }
}
