include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../StandardLibrary/IO.dfy"
include "UTF8.dfy"

module {:extern "ToyUTF8Transform"} ToyUTF8Transform {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import IO
  import Collections
  import UTF8

  // ToyEnumerator wraps and operates on an BlockingNativeEnumerator
  // Implements a toy example where we interpret read bytes as UTF8, duplicate
  // each character (e.g. "abc" -> "aabbcc"), reencode the UTF8, and return those bytes.
  class ToyEnumerator extends Collections.Enumerator<seq<uint8>> {
    // Currently this specifies an BlockingNativeEnumerator because we want to guarantee that
    // we always get some bytes back on Next. This is needed in order to prove termination
    // in the Dafny code (note that this just moves the termination concern into the extern).
    // I see three possible paths forward here:
    //    1. Don't prove termination in the Dafny code (this is honest, though we lose out an verifiying that
    //       nothing specifically in the Dafny code results in some infinite loop)
    //    2. Define a slightly more restrictive trait that extends Enumerator<seq<T>> with this property and use that 
    var source: IO.BlockingNativeEnumerator 
    var utf8Transform: UTF8Transformer
    var sourceDone: bool

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && this in Repr 
      && source in Repr && source.Repr <= Repr && this !in source.Repr && source.Valid()
      && utf8Transform in Repr && utf8Transform.Repr <= Repr && this !in utf8Transform.Repr && utf8Transform.Valid()
      && utf8Transform.Repr !! source.Repr
    }

    constructor (source: IO.BlockingNativeEnumerator)
      requires source.Valid() 
      ensures this.source == source
      ensures !hasFailed
      ensures !signaledDone
      ensures Valid() && fresh(Repr - source.Repr - utf8Transform.Repr)
    {
      this.source := source;
      this.sourceDone := false;
      this.hasFailed := false;
      this.signaledDone := false;
      var utf8Transform := new UTF8Transformer();
      this.utf8Transform := utf8Transform;
      this.Repr := {this} + source.Repr + utf8Transform.Repr;
    }

    method Next() returns (element: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(signaledDone) || old(hasFailed) ==> element.Failure?
      ensures element.Failure? ==> hasFailed
      ensures element.Success? && element.value.None? ==> signaledDone
      // Ideally we could have condition here that describe the
      // transformation we want, however this is based upon input
      // that we don't get until runtime. Therefore, we verify
      // that the Transform by itself is correct. Ideally we could
      // leave less unspecified in this method
    {
      if signaledDone {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      }

      // Need to pull from the source and transform until we get back
      // at least one byte to return, or Done
      while true
        decreases 4 - |utf8Transform.inBuffer|;
        invariant Valid()
        invariant old(Repr) == Repr
      {
        // Read from source
        var res := source.Next();
        if res.Failure? {
          hasFailed := true;
          return Failure("Failed to read source");
        } else if res.value.None? {
          // Source is at EOF, we should trigger EOF through transformer
          // and return the result
          sourceDone := true;
          var transformed := utf8Transform.Final();
          if transformed.Failure? {
            hasFailed := true;
            return Failure("Failed to end encryption operation");
          }
          signaledDone := true;
          return Success(None());
        }

        // Transform bytes read from source
        var transformed := utf8Transform.Transform(res.value.get);
        if transformed.Failure? {
          hasFailed := true;
          return Failure("Failed to transform bytes");
        } else if transformed.Success? && transformed.value.Some? {
          return Success(Some(transformed.value.get));
        }
      }
    }
  }
  
  // ToyAggregator wraps and operates on an Aggregator
  // Implements a toy example where we interpret input bytes as UTF8, duplicate
  // each character (e.g. "abc" -> "aabbcc"), reencode the UTF8, and write those bytes.
  class ToyAggregator extends Collections.Aggregator<seq<uint8>> {
    // Again, we specify using BlockingNativeAggregator instead of Aggregator
    // because we want to be able to prove termination, and that requires
    // restricting the interface from allowing "wait"s.
    // Couple other solutions:
    //    1. Check during runtime and fail if Success(false) is returned
    //    2. Remove termination requirement from interface
    //    3. Remove "wait" from interface
    //    4. Define new "blocking" trait with this property which extends Aggregator
    var sink: IO.BlockingNativeAggregator
    var utf8Transform: UTF8Transformer

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && this in Repr 
      && sink in Repr && sink.Repr <= Repr && this !in sink.Repr && sink.Valid()
      && utf8Transform in Repr && utf8Transform.Repr <= Repr && this !in utf8Transform.Repr && utf8Transform.Valid()
      && utf8Transform.Repr !! sink.Repr
    }

    constructor (sink: IO.BlockingNativeAggregator)
      requires sink.Valid() 
      ensures this.sink == sink
      ensures !hasFailed
      ensures !done
      ensures Valid() && fresh(Repr - sink.Repr - utf8Transform.Repr)
    {
      this.sink := sink;
      this.hasFailed := false;
      this.done := false;
      var utf8Transform := new UTF8Transformer();
      this.utf8Transform := utf8Transform;
      this.Repr := {this} + sink.Repr + utf8Transform.Repr;
    }

    method Accept(element: seq<uint8>) returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      // Ideally we could have condition here that describe the
      // transformation we want, however we have no way to look
      // into what was written by the underlying Aggregator (it
      // is impossible to do so and remain generic about the sink).
      // Therefore, we verify that the Transform by itself is correct.
      // Ideally we could leave less unspecified in this method
    {
      if done {
        hasFailed := true;
        return Failure("Enumerator is at EOF and cannot be read.");
      } else if hasFailed {
        return Failure("Enumerator is in a failed state.");
      }

      var transformedChunk := utf8Transform.Transform(element);
      if transformedChunk.Failure? {
        hasFailed := true;
        return Failure("Failed to transform input");
      } else if transformedChunk.value.None? {
        // successfully accepted bytes into buffer, but not enough
        // to write tranformation sink.
        return Success(true);
      }
      
      // Write the transformed bytes to the sink
      res := sink.Accept(transformedChunk.value.get);
      if res.Failure? {
        hasFailed := true;
        return Failure("Failed to write bytes to underlying sink.");
      }
      // There isn't a way to assert this as a postcondition on the method,
      // but make sure that these bytes were actually written
      // TODO: This seems like an easy miss.
      assert res.Success? && res.value;

      return res;
    }

    method End() returns (res: Result<bool>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
      ensures res.Success? && res.value ==> done
    {
      if done {
        hasFailed := true;
        return Failure("The Aggregator has already completed.");
      } else if hasFailed {
        return Failure("The Aggregator is in a failed state.");
      }

      // End transformer. In our case, this will fail if extra bytes are in the buffer
      var transformed := utf8Transform.Final();
      if transformed.Failure? {
        hasFailed := true;
        return Failure("Failed to end transform due to extra invalid bytes");
      } else if transformed.value.Some? {
        // write final bytes to sink
        var acceptRes := sink.Accept(transformed.value.get);
        if acceptRes.Failure? {
          hasFailed := true;
          return Failure("Failled to write to sink");
        } 
        assert acceptRes.value;
      }

      // Signify End to Sink
      res := sink.End();
      if res.Failure? {
        hasFailed := true;
        return Failure("Failed to End underlying sink.");
      }
    
      // TODO Same as above, this seems easy to not check
      assert res.Success? && res.value;

      done := true;
      return res;
    }
  }

  // Represents a stateful transformation of streamed input into transformed output.
  // Maintains a buffer of inputted bytes, interprets those bytes as UTF8, and returns a sequence of bytes
  // representing the encoding of those UTF8 characters doubled. E.g.: UTF8.Decode("abc") -> UTF8.Decode("aabbcc").
  class UTF8Transformer {
    ghost const Repr: set<object>
    var done: bool
    var hasFailed: bool
    var inBuffer: seq<uint8>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
    {
      && this in Repr 
      && |inBuffer| < 4
    }

    constructor ()
      ensures !hasFailed
      ensures !done
      ensures inBuffer == []
      ensures Valid() && fresh(Repr)
    {
      this.hasFailed := false;
      this.done := false;
      this.inBuffer := [];
      this.Repr := {this};
    }

    // Transforms inputted bytes into transformed output, and maintains a buffer of bytes for the input that
    // is not yet transformed.
    // If this method does not have enough bytes to interpret at least one UTF8 character, returns Success(None).
    // If this method has enough bytes to determine that an invalid UTF8 encoding was inputted, returns Failure().
    method Transform(element: seq<uint8>) returns (transformed: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures old(done) || old(hasFailed) ==> transformed.Failure?
      ensures transformed.Failure? ==> hasFailed
      // Note: It is very difficult to reason about the exact transform here due to the fact that UTF8.Encode/Decode goes to an
      // extern method, meaning that we don't have any tools to reason about how we expect those transformations to go.
      // Regardless, we can still specify things such that the below to at least ensure we do not fail on good inputs
      ensures transformed.Success? && transformed.value.None? ==> |inBuffer| == |element| + |old(inBuffer)|
      ensures transformed.Success? && transformed.value.Some? ==> UTF8.ValidUTF8Seq(transformed.value.get)
      ensures
        var newBuffer := old(inBuffer) + element;
        && (!done && !hasFailed && |old(inBuffer)+element| > 0 && UTF8.ValidUTF8Seq(newBuffer) ==> transformed.Success? && transformed.value.Some?)
        && (!done && !hasFailed && |old(inBuffer)+element| > 1 && UTF8.ValidUTF8Seq(newBuffer[..|newBuffer| - 1]) ==> transformed.Success? && transformed.value.Some?)
        && (!done && !hasFailed && |old(inBuffer)+element| > 2 && UTF8.ValidUTF8Seq(newBuffer[..|newBuffer| - 2]) ==> transformed.Success? && transformed.value.Some?)
        && (!done && !hasFailed && |old(inBuffer)+element| > 3 && UTF8.ValidUTF8Seq(newBuffer[..|newBuffer| - 3]) ==> transformed.Success? && transformed.value.Some?)
    {
      if done {
        hasFailed := true;
        return Failure("Transformer is at EOF and cannot transform any more.");
      } else if hasFailed {
        return Failure("Transformer is in a failed state.");
      }

      // This is a quick (to implement) and dirty way to determine what segment of the inBuffer is valid UTF8.
      // We can assume that the first index is always the beginning of a UTF8 charactera, but we need
      // to pick a slice such that the end index doesn't cut in the middle of a multi-byte UTF8 character.
      // UTF8 characters can be up to four bytes, so just brute force by checking the last four indexes.
      // If none of these work, then we know that the inputted bytes were not valid UTF8.
      // If we don't have four bytes yet, and the indexes we do have aren't valid, return Success(None())
      inBuffer := inBuffer + element;
      assert inBuffer == old(inBuffer) + element;
      var endIndex;
      if (|inBuffer| > 0 && UTF8.ValidUTF8Seq(inBuffer)) {
        endIndex := |inBuffer|;
        assert inBuffer == inBuffer[..endIndex];
        assert UTF8.ValidUTF8Seq(inBuffer[..endIndex]);
      } else if (|inBuffer| > 1 && UTF8.ValidUTF8Seq(inBuffer[..|inBuffer| - 1])) {
        endIndex := |inBuffer| - 1;
        assert UTF8.ValidUTF8Seq(inBuffer[..endIndex]);
      } else if (|inBuffer| > 2 && UTF8.ValidUTF8Seq(inBuffer[..|inBuffer| - 2])) {
        endIndex := |inBuffer| - 2;
        assert UTF8.ValidUTF8Seq(inBuffer[..endIndex]);
      } else if (|inBuffer| > 3 && UTF8.ValidUTF8Seq(inBuffer[..|inBuffer| - 3])) {
        endIndex := |inBuffer| - 3;
        assert UTF8.ValidUTF8Seq(inBuffer[..endIndex]);
      } else if |inBuffer| > 3 {
        // if we get here, then the bytes we are reading are invalid UTF8
        hasFailed := true;
        inBuffer := [];
        return Failure("Encountered invalid UTF8 bytes");
      } else {
        // otherwise, we don't have enough bytes to perform the transformatoin
        // theyre already in the buffer, so return Success(None)
        return Success(None());
      }

      // grab the chunk of bytes we want to work with and update the buffer
      var chunkToManipulate := inBuffer[..endIndex];
      inBuffer := inBuffer[endIndex..];

      // Convert the chunk from UTF8 bytes -> string
      var decodeRes := UTF8.Decode(chunkToManipulate);
      if decodeRes.Failure? {
        hasFailed := true;
        return Failure("UTF8 Decoder encountered Failure: " + decodeRes.error);
      }
      var decodedChunk := decodeRes.value;

      // iterate through decoded string to create new string which duplicates the characters
      var chunkIndex := 0;
      var doubledChunk := "";
      while chunkIndex < |decodedChunk|
      {
        doubledChunk := doubledChunk + [decodedChunk[chunkIndex], decodedChunk[chunkIndex]];
        chunkIndex := chunkIndex + 1;
      }

      // Convert back to bytes
      var encodeRes := UTF8.Encode(doubledChunk);
      if encodeRes.Failure? {
        hasFailed := true;
        return Failure("UTF8 Decoder encountered Failure: " + encodeRes.error);
      }
      var transformedChunk := encodeRes.value;
      
      // Return transformed bytes
      return Success(Some(transformedChunk));
    }

    // Signifies the end of the transformer, processing any bytes remaining in the buffer
    // and returning the final transformed bytes.
    // If this method does not have enough bytes in the buffer to complete the transformation,
    // returns Failure().
    // Once called, UTF8Transformer will faill all future Final() or Transform() calls.
    // Note: for this transform we never have final bytes to return, however I am modeling
    // this such that bytes could be returned since we will need that behavior for the ESDK Encrypt/Decrypt
    method Final() returns (res: Result<Option<seq<uint8>>>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures res.Success? ==> done
      ensures old(done) || old(hasFailed) ==> res.Failure?
      ensures res.Failure? ==> hasFailed
    {
      if done {
        hasFailed := true;
        return Failure("The Aggregator has already completed.");
      } else if hasFailed {
        return Failure("The Aggregator is in a failed state.");
      }

      // If we still have things in the inBuffer, then the bytes inputted were not valid UTF8.
      if |inBuffer| > 0 {
        hasFailed := true;
        return Failure("Invalid UTF8 bytes supplied to transformer.");
      }

      // Otherwise, we don't have any bytes to return, so return Success(None)
      done := true;
      return Success(None());
    }
  }
}
