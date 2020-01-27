include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  iterator SeqIter<T>(s: seq<T>) yields (x : T)
    yield ensures x in s
    yield ensures |xs| <= |s|
    yield ensures xs == s[..|xs|]
    yield ensures fresh(_new)
    ensures fresh(_new)
  {
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant idx == |xs|
      invariant xs <= s
    {
      x := s[idx];
      yield;
      idx := idx + 1;
    }
  }

  method ReadBytes(iter: SeqIter<uint8>, n: nat) returns (res: Result<seq<uint8>>)
    requires n > 0
    requires iter.Valid()
    modifies iter, iter._new, iter._modifies
    ensures res.Success? ==> |res.value| == n
  {
    var bytes := [];
    var i := 0;
    var more := true;
    while i < n
      invariant 0 <= i <= n
      invariant i == |bytes|
      invariant iter.Valid() && fresh(iter._new)
    {
      more := iter.MoveNext();
      if (!more) { return Failure("IO Error: Not enough bytes left on stream."); }
      bytes := bytes + [iter.x];
      i := i + 1;
    }
    return Success(bytes);
  }

  method ReadByte(iter: SeqIter<uint8>) returns (res: Result<uint8>)
    requires iter.Valid()
    modifies iter, iter._new, iter._modifies
  {
    var readBytes :- ReadBytes(iter, 1);
    assert |readBytes| == 1;
    return Success(readBytes[0]);
  }

  method ReadUInt16(iter: SeqIter<uint8>) returns (res: Result<uint16>)
    requires iter.Valid()
    modifies iter, iter._new, iter._modifies
  {
    var readBytes :- ReadBytes(iter, 2);
    assert |readBytes| == 2;
    var n := SeqToUInt16(readBytes);
    return Success(n);
  }

  method ReadUInt32(iter: SeqIter<uint8>) returns (res: Result<uint32>)
    requires iter.Valid()
    modifies iter, iter._new, iter._modifies
  {
    var readBytes :- ReadBytes(iter, 4);
    assert |readBytes| == 4;
    var n := SeqToUInt32(readBytes);
    return Success(n);
  }

  class StringWriter {
    var data: seq<uint8>  // TODO: make "data" ghost and provide an implementation that writes to an array

    ghost var Repr: set<object>

    predicate Valid()
      reads this
    {
      this in Repr
    }

    predicate method HasRemainingCapacity(n: nat)  // Compare with an upper bound on the amount of data the stream can accept on Write
      requires Valid()
      reads this
    {
      // TODO: revisit this definition if we change the backing store of the StringWriter to be something with limited capacity
      true
    }

    constructor()
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method WriteSeq(bytes: seq<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(lengthWritten) =>
          && old(HasRemainingCapacity(|bytes|))
          && lengthWritten == |bytes|
          && data == old(data) + bytes
        case Failure(e) => unchanged(`data)
    {
      if HasRemainingCapacity(|bytes|) {
        data := data + bytes;
        return Success(|bytes|);
      } else {
        return Failure("IO Error: Stream capacity exceeded.");
      }
    }

    method WriteByte(n: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(lengthWritten) =>
          && old(HasRemainingCapacity(1))
          && lengthWritten == 1
          && data == old(data) + [n]
        case Failure(e) => unchanged(`data)
    {
      if HasRemainingCapacity(1) {
        data := data + [n];
        return Success(1);
      } else {
        return Failure("IO Error: Stream capacity exceeded.");
      }
    }

    method WriteUInt16(n: uint16) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(lengthWritten) =>
          && old(HasRemainingCapacity(2))
          && lengthWritten == 2
          && data == old(data) + UInt16ToSeq(n)
        case Failure(e) => unchanged(`data)
    {
      if HasRemainingCapacity(2) {
        data := data + UInt16ToSeq(n);
        return Success(2);
      } else {
        return Failure("IO Error: Stream capacity exceeded.");
      }
    }

    method WriteUInt32(n: uint32) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(lengthWritten) =>
          && old(HasRemainingCapacity(4))
          && lengthWritten == 4
          && data == old(data) + UInt32ToSeq(n)
        case Failure(e) => unchanged(`data)
    {
      if HasRemainingCapacity(4) {
        data := data + UInt32ToSeq(n);
        return Success(4);
      } else {
        return Failure("IO Error: Stream capacity exceeded.");
      }
    }
  }
}
