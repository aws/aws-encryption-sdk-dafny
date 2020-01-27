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
      ensures fresh(Repr - {this})
    {
      this.data := s;
      this.pos := 0;
      Repr := {this};
    }

    method ReadBytes(byteCount: nat) returns (bytes: seq<T>)
      requires byteCount + pos <= |data|
      requires Valid()
      modifies Repr
      ensures byteCount == 0 ==> bytes == []
      ensures byteCount > 0 ==> bytes == data[old(pos)..][..byteCount]
      ensures pos == old(pos) + byteCount
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      bytes := data[pos..][..byteCount];
      pos := pos + byteCount;
      Repr := {this};
      return bytes;
    }

    method ReadExact(n: nat) returns (res: Result<seq<T>>)
      requires Valid()
      modifies Repr
      ensures res.Success? ==> |res.value| == n
      ensures res.Failure? ==> n > |data| - pos
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      if n > |data| - pos {
        return Failure("IO Error: Not enough bytes left on stream.");
      } else {
        var bytes := ReadBytes(n);
        Repr := {this};
        return Success(bytes);
      }
    }
  }

  class ByteReader {
    ghost var Repr: set<object>
    var memReader: MemoryReader<uint8>

    predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (memReader in Repr && memReader.Repr <= Repr && memReader.Valid())
    }

    constructor(m: MemoryReader<uint8>)
      requires m.Valid()
      ensures memReader == m
      ensures Valid()
    {
      memReader := m;
      Repr := {this} + {m} + m.Repr;
    }

    method ReadByte() returns (res: Result<uint8>)
      requires Valid()
      modifies Repr
      ensures res.Failure? ==> |memReader.data| - memReader.pos < 1
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      var bytes :- memReader.ReadExact(1);
      assert |bytes| == 1;
      Repr := Repr + {memReader} + memReader.Repr;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>>)
      requires Valid()
      modifies Repr
      ensures res.Failure? ==> |memReader.data| - memReader.pos < n
      ensures res.Success? ==> |res.value| == n
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      var bytes :- memReader.ReadExact(n);
      Repr := Repr + {memReader} + memReader.Repr;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16>)
      requires Valid()
      modifies Repr
      ensures res.Failure? ==> |memReader.data| - memReader.pos < 2
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      var bytes :- memReader.ReadExact(2);
      var n := SeqToUInt16(bytes);
      Repr := Repr + {memReader} + memReader.Repr;
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32>)
      requires Valid()
      modifies Repr
      ensures res.Failure? ==> |memReader.data| - memReader.pos < 4
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      var bytes :- memReader.ReadExact(4);
      var n := SeqToUInt32(bytes);
      Repr := Repr + {memReader} + memReader.Repr;
      return Success(n);
    }

    function method GetRemainingCapacity(): (n: nat)
      reads Repr
      requires Valid()
      ensures Valid()
      ensures n == |memReader.data| - memReader.pos
    {
      |memReader.data| - memReader.pos
    }

    function method GetUsedCapacity(): (n: nat)
      reads Repr
      requires Valid()
      ensures Valid()
      ensures n == memReader.pos
    {
      memReader.pos
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
