// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"

module Streams {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  class SeqReader<T> {
    ghost var Repr: set<object>
    const data: seq<T>
    var pos: nat

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      pos <= |data|
    }

    constructor (s: seq<T>)
      ensures pos == 0
      ensures data[..] == s
      ensures Valid() && fresh(Repr)
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

    method ReadExact(n: nat) returns (res: Result<seq<T>, string>)
      requires Valid()
      modifies `pos
      ensures n + old(pos) <= |data| <==> res.Success?
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? ==> pos == old(pos) + n
      ensures res.Success? ==> res.value == data[old(pos)..old(pos) + n]
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
    const reader: SeqReader<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      reader in Repr && reader.Repr <= Repr && this !in reader.Repr && reader.Valid()
    }

    constructor (s: seq<uint8>)
      ensures reader.data == s
      ensures reader.pos == 0
      ensures Valid() && fresh(Repr)
    {
      var mr := new SeqReader<uint8>(s);
      reader := mr;
      Repr := {this} + mr.Repr;
    }

    method ReadByte() returns (res: Result<uint8, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 1
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 1
      ensures old(reader.pos) + 1 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos)]
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(1);
      assert |bytes| == 1;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < n
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? && |res.value| == 0 ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + n
      ensures old(reader.pos) + n <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos)..old(reader.pos) + n]
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(n);
      assert |bytes| == n;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 2
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 2
      ensures old(reader.pos) + 2 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt16(reader.data[old(reader.pos)..old(reader.pos) + 2])
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(2);
      assert |bytes| == 2;
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32, string>)
      requires Valid()
      modifies reader`pos
      ensures Valid()
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==>
        && reader.pos == old(reader.pos) + 4
        && UInt32ToSeq(res.value) == reader.data[old(reader.pos)..reader.pos]
    {
      var bytes :- reader.ReadExact(4);
      assert |bytes| == 4;
      var n := SeqToUInt32(bytes);
      UInt32SeqDeserializeSerialize(bytes);
      return Success(n);
    }

    method ReadUInt64() returns (res: Result<uint64, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 8
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 8
      ensures old(reader.pos) + 8 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt64(reader.data[old(reader.pos)..old(reader.pos) + 8])
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(8);
      assert |bytes| == 8;
      var n := SeqToUInt64(bytes);
      return Success(n);
    }

    method IsDoneReading() returns (b: bool)
      requires Valid()
      ensures (b && |reader.data| - reader.pos == 0) || (!b && |reader.data| - reader.pos > 0)
      ensures Valid()
    {
      return |reader.data| == reader.pos;
    }

    method GetSizeRead() returns (n: nat)
      requires Valid()
      ensures n == reader.pos
      ensures Valid()
    {
      return reader.pos;
    }
  }

  class SeqWriter<T> {
    ghost var Repr: set<object>
    var data: seq<T>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }

    constructor()
      ensures data == []
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method WriteElements(elems: seq<T>) returns (n: nat)
      requires Valid()
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
  }

  class ByteWriter {
    ghost var Repr: set<object>
    const writer: SeqWriter<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      writer in Repr && writer.Repr <= Repr && this !in writer.Repr && writer.Valid()
    }

    constructor()
      ensures writer.data == []
      ensures Valid() && fresh(Repr)
    {
      var mw := new SeqWriter<uint8>();
      writer := mw;
      Repr := {this} + mw.Repr;
    }

    method WriteByte(n: uint8) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + [n]
      ensures r == 1
      ensures Valid()
    {
      r := writer.WriteElements([n]);
    }

    method WriteBytes(s: seq<uint8>) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + s
      ensures r == |s|
      ensures Valid()
    {
      r := writer.WriteElements(s);
    }

    method WriteUInt16(n: uint16) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt16ToSeq(n)
      ensures r == 2
      ensures Valid()
    {
      r := writer.WriteElements(UInt16ToSeq(n));
    }

    method WriteUInt32(n: uint32) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt32ToSeq(n)
      ensures r == 4
      ensures Valid()
    {
      r := writer.WriteElements(UInt32ToSeq(n));
    }

    function method GetDataWritten(): (s: seq<uint8>)
      reads Repr
      requires Valid()
      ensures s == writer.data
      ensures Valid()
    {
      writer.data
    }

    function method GetSizeWritten(): (n: nat)
      reads Repr
      requires Valid()
      ensures n == |writer.data|
      ensures Valid()
    {
      |writer.data|
    }
  }
}
