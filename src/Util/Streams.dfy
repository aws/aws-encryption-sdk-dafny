include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  class SeqReader<T> {
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
    var reader: SeqReader<uint8>

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
      var mr := new SeqReader<uint8>(s);
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

  class SeqWriter<T> {
    ghost var Repr: set<object>
    const maxSize: nat
    var data: seq<T>

    predicate Valid() reads this, Repr
    {
      Repr == {this} &&
      |data| <= maxSize
    }

    constructor(n: nat)
      ensures maxSize == n
      ensures data == []
      ensures Valid()
    {
      maxSize := n;
      data := [];
      Repr := {this};
    }

    method WriteElements(elems: seq<T>) returns (n: nat)
      requires Valid()
      requires maxSize >= (|elems| + |data|)
      modifies `data
      ensures n == |data| - |old(data)| == |elems|
      ensures |elems| == 0 ==> data == old(data)
      ensures |elems| > 0 ==> data == old(data) + elems
      ensures elems == data[(|data| - |elems|)..]
      ensures Valid()
    {
      data := data + elems;
      return |elems|;
    }

    method WriteExact(elems: seq<T>) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures res.Success? ==> res.value == |data| - |old(data)| == |elems|
      ensures res.Success? ==> data == old(data) + elems
      ensures res.Success? && |elems| > 0 ==> !unchanged(`data)
      ensures res.Success? && |elems| == 0 ==> unchanged(`data)
      ensures res.Failure? ==> maxSize < (|elems| + |data|)
      ensures res.Failure? ==> unchanged(`data)
      ensures maxSize == old(maxSize)
      ensures Valid()
    {
      if maxSize < (|elems| + |data|) {
        return Failure("IO Error: Stream capacity exceeded.");
      } else {
        var totalWritten := WriteElements(elems);
        return Success(totalWritten);
      }
    }
  }

  class ByteWriter {
    ghost var Repr: set<object>
    var writer: SeqWriter<uint8>

    predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (writer in Repr && writer.Repr <= Repr && writer.Valid())
    }

    constructor(n: nat)
      ensures writer.maxSize == n
      ensures n == old(n)
      ensures fresh(Repr - {this})
      ensures Valid()
    {
      var mw := new SeqWriter<uint8>(n);
      writer := mw;
      Repr := {this} + {writer} + mw.Repr;
    }

    method WriteByte(n: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies writer`data
      ensures res.Failure? ==> |writer.data| + 1 > writer.maxSize
      ensures res.Failure? ==> unchanged(writer)
      ensures res.Success? ==> !unchanged(writer`data)
      ensures res.Success? ==> writer.data == old(writer.data) + [n]
      ensures res.Success? ==> res.value == 1
      ensures writer.maxSize == old(writer.maxSize)
      ensures Valid()
    {
      var written :- writer.WriteExact([n]);
      return Success(written);
    }

    method WriteBytes(s: seq<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies writer`data
      ensures res.Failure? ==> |writer.data| + |s| > writer.maxSize
      ensures res.Failure? ==> unchanged(writer)
      ensures res.Success? && |s| == 0 ==> unchanged(writer)
      ensures res.Success? && |s| > 0 ==> !unchanged(writer`data)
      ensures res.Success? ==> writer.data == old(writer.data) + s
      ensures res.Success? ==> res.value == |s|
      ensures writer.maxSize == old(writer.maxSize)
      ensures Valid()
    {
      var written :- writer.WriteExact(s);
      return Success(written);
    }

    method WriteUInt16(n: uint16) returns (res: Result<nat>)
      requires Valid()
      modifies writer`data
      ensures res.Failure? ==> |writer.data| + 2 > writer.maxSize
      ensures res.Failure? ==> unchanged(writer)
      ensures res.Success? ==> !unchanged(writer`data)
      ensures res.Success? ==> writer.data == old(writer.data) + UInt16ToSeq(n)
      ensures res.Success? ==> res.value == 2
      ensures writer.maxSize == old(writer.maxSize)
      ensures Valid()
    {
      var written :- writer.WriteExact(UInt16ToSeq(n));
      return Success(written);
    }

    method WriteUInt32(n: uint32) returns (res: Result<nat>)
      requires Valid()
      modifies writer`data
      ensures res.Failure? ==> |writer.data| + 4 > writer.maxSize
      ensures res.Failure? ==> unchanged(writer)
      ensures res.Success? ==> !unchanged(writer`data)
      ensures res.Success? ==> writer.data == old(writer.data) + UInt32ToSeq(n)
      ensures res.Success? ==> res.value == 4
      ensures writer.maxSize == old(writer.maxSize)
      ensures Valid()
    {
      var written :- writer.WriteExact(UInt32ToSeq(n));
      return Success(written);
    }
  }
}
