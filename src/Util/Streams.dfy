include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  class StringReader {
    const data: array<uint8>
    var pos: nat

    ghost var Repr: set<object>

    predicate Valid()
      reads this
    {
      this in Repr &&
      data in Repr &&
      pos <= data.Length
    }

    function method Available(): nat  // An upper bound on the amount of data the stream can deliver on Read
      requires Valid()
      reads this
    {
      data.Length - pos
    }

    constructor(d: array<uint8>)
      ensures Valid()
    {
      Repr := {this, d};
      data := d;
      pos := 0;
    }

    method Read(arr: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && arr != data
      requires off + req <= arr.Length
      modifies this, arr
      ensures Valid()
      ensures var n := min(req, old(Available()));
        arr[..] == arr[..off] + data[old(pos) .. (old(pos) + n)] + arr[off + n ..]
      ensures match res
        case Success(lengthRead) => lengthRead == min(req, old(Available()))
        case Failure(e) => unchanged(this) && unchanged(arr)
    {
      var n := min(req, Available());
      forall i | 0 <= i < n {
        arr[off + i] := data[pos + i];
      }
      pos := pos + n;
      return Success(n);
    }

    method ReadSeq(desiredByteCount: nat) returns (bytes: seq<uint8>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures bytes == data[old(pos)..][..min(desiredByteCount, old(Available()))]
    {
      var n := min(desiredByteCount, Available());
      bytes := seq(n, i requires 0 <= i < n && pos + n <= data.Length reads this, data => data[pos + i]);
      pos := pos + n;
    }

    // Read exactly `n` bytes, if possible; otherwise, fail.
    method ReadExact(n: nat) returns (res: Result<seq<uint8>>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures match res
        case Success(bytes) => |bytes| == n
        case Failure(_) => true
    {
      var bytes := ReadSeq(n);
      if |bytes| != n {
        return Failure("IO Error: Not enough bytes left on stream.");
      } else {
        return Success(bytes);
      }
    }

    // Read exactly 1 byte, if possible, and return as a uint8; otherwise, fail.
    method ReadByte() returns (res: Result<uint8>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(1);
      var n := bytes[0];
      return Success(n);
    }

    // Read exactly 2 bytes, if possible, and return as a uint16; otherwise, fail.
    method ReadUInt16() returns (res: Result<uint16>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(2);
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    // Read exactly 4 bytes, if possible, and return as a uint32; otherwise, fail.
    method ReadUInt32() returns (res: Result<uint32>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(4);
      var n := SeqToUInt32(bytes);
      return Success(n);
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

    method Write(a: array<uint8>, off: nat, len: nat) returns (res: Result<nat>)
      requires Valid() && a !in Repr
      requires off + len <= a.Length
      modifies `data
      ensures Valid()
      ensures match res
        case Success(lengthWritten) =>
          && old(HasRemainingCapacity(len))
          && lengthWritten == len
          && data == old(data) + a[off..][..len]
        case Failure(e) => unchanged(`data)
    {
      if HasRemainingCapacity(len) {
        data := data + a[off..off + len];
        return Success(len);
      } else {
        return Failure("IO Error: Stream capacity exceeded.");
      }
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
