include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  class MemoryReader<T> {
    ghost var Repr: set<object>
    const data: seq<T>
    var pos: nat

    predicate Valid() reads this, Repr
    {
      Repr == {this} &&
      pos <= |data|
    }

    constructor(s: seq<T>)
      ensures pos == 0
      ensures data[..] == s
      ensures Valid()
    {
      data := s;
      pos := 0;
      Repr := {this};
    }

    method ReadElements(n: nat) returns (elems: seq<T>)
      requires Valid()
      requires n + pos <= |data|
      modifies `pos
      ensures n == 0 ==> elems == []
      ensures n > 0 ==> elems == data[old(pos)..][..n]
      ensures pos == old(pos) + n
      ensures data == old(data)
      ensures Valid()
    {
      elems := data[pos..][..n];
      pos := pos + n;
      return elems;
    }

    method ReadExact(n: nat) returns (res: Result<seq<T>>)
      requires Valid()
      modifies `pos
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? ==> pos == old(pos) + n
      ensures res.Failure? ==> n > |data| - pos
      ensures res.Failure? ==> pos == old(pos)
      ensures data == old(data)
      ensures Valid()
    {
      if n > |data| - pos {
        return Failure("IO Error: Not enough elements left on stream.");
      } else {
        var elements := ReadElements(n);
        return Success(elements);
      }
    }
  }

  class ByteReader {
    ghost var Repr: set<object>
    var reader: MemoryReader<uint8>

    predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (reader in Repr && reader.Repr <= Repr && reader.Valid())
    }

    constructor(s: seq<uint8>)
      ensures reader.data == s
      ensures s == old(s)
      ensures fresh(Repr - {this})
      ensures Valid()
    {
      var mr := new MemoryReader<uint8>(s);
      reader := mr;
      Repr := {this} + {reader} + mr.Repr;
    }

    method ReadByte() returns (res: Result<uint8>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 1
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> !unchanged(reader`pos)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 1
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(1);
      assert |bytes| == 1;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < n
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? && |res.value| == 0 ==> unchanged(reader)
      ensures res.Success? && |res.value| > 0 ==> !unchanged(reader`pos)
      ensures res.Success? ==> reader.pos == old(reader.pos) + n
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(n);
      assert |bytes| == n;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 2
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> !unchanged(reader`pos)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 2
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(2);
      assert |bytes| == 2;
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 4
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> !unchanged(reader`pos)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 4
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(4);
      assert |bytes| == 4;
      var n := SeqToUInt32(bytes);
      return Success(n);
    }

    function method GetRemainingCapacity(): (n: nat)
      reads Repr
      requires Valid()
      ensures n == |reader.data| - reader.pos
      ensures Valid()
    {
      |reader.data| - reader.pos
    }

    function method GetUsedCapacity(): (n: nat)
      reads Repr
      requires Valid()
      ensures n == reader.pos
      ensures Valid()
    {
      reader.pos
    }
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
