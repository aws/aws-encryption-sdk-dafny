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
      if off == arr.Length || Available() == 0 {
        assert (min (req, Available())) == 0;
        return Success(0);
      } else {
        var n := min(req, Available());
        forall i | 0 <= i < n {
          arr[off + i] := data[pos + i];
        }
        pos := pos + n;
        return Success(n);
      }
    }

    method ReadSeq(req: nat) returns (res: Result<seq<uint8>>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures match res
        case Success(bytes) => bytes == data[old(pos)..][..min(req, old(Available()))]
        case Failure(e) => unchanged(this)
    {
      var n := min(req, Available());
      var bytes := seq(n, i requires 0 <= i < n && pos + n <= data.Length reads this, data => data[pos + i]);
      pos := pos + n;
      return Success(bytes);
    }

    // Read exactly `n` bytes, if possible; otherwise, fail.
    method ReadExact(n: nat) returns (ret: Result<seq<uint8>>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures match ret
        case Success(bytes) => |bytes| == n
        case Failure(_) => true
    {
      var bytes :- ReadSeq(n);
      if |bytes| != n {
        return Failure("IO Error: Not enough bytes left on stream.");
      } else {
        return Success(bytes);
      }
    }

    // Read exactly 2 bytes, if possible, and return as a uint16; otherwise, fail.
    method ReadUInt16() returns (ret: Result<uint16>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(2);
      var n := SeqToUInt16(bytes);
      return Success(n);
    }
  }

  class StringWriter {
    ghost var data: seq<uint8>

    ghost var Repr: set<object>

    predicate Valid()
      reads this
    {
      this in Repr
    }

    function method Capacity(): nat  // An upper bound on the amount of data the stream can accept on Write
      requires Valid()
      reads this
    {
      0 // TODO?
    }

    constructor()
      ensures Valid()
    {
      data := [];
      Repr := {this};
    }

    method Write(a: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && a !in Repr
      requires off + req <= a.Length
      modifies `data
      ensures Valid()
      ensures match res
        case Success(len_written) =>
          if old(Capacity()) == 0 then
            len_written == 0
          else
            && len_written == min(req, old(Capacity()))
            && data == old(data) + a[off..off+req]
        case Failure(e) => true
    {
      if off == a.Length || Capacity() == 0 {
        return Success(0);
      } else {
        var n := min(req, Capacity());
        data := data + a[off..off+req];
        return Success(n);
      }
    }

    method WriteSimple(a: array<uint8>) returns (res: Result<nat>)
      requires Valid() && a !in Repr
      modifies `data
      ensures Valid()
      ensures match res
        case Success(len_written) =>
            && len_written == a.Length
            && data[..] == old(data) + a[..]
        case Failure(e) => unchanged(`data)
    {
      if a.Length <= Capacity() {
        data := data + a[..];
        return Success(a.Length);
      } else {
        return Failure("IO Error: Reached end of stream.");
      }
    }

    method WriteSimpleSeq(a: seq<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(len_written) =>
            && len_written == |a|
            && data[..] == old(data) + a
        case Failure(e) => unchanged(`data)
    {
      if |a| <= Capacity() {
        data := data + a;
        return Success(|a|);
      } else {
        return Failure("IO Error: Reached end of stream.");
      }
    }

    method WriteSingleByte(a: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(len_written) =>
          if old(Capacity()) == 0 then
            len_written == 0
          else
            && len_written == 1
            && data == old(data) + [a]
            // Dafny->Boogie drops an old: https://github.com/dafny-lang/dafny/issues/320
            //&& data[..] == old(data)[.. old(pos)] + [a] + old(data)[old(pos) + 1 ..]
        case Failure(e) => unchanged(`data)
    {
      if Capacity() == 0 {
        return Success(0);
      } else {
        data := data + [a];
        return Success(1);
      }
    }

    method WriteSingleByteSimple(a: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res
        case Success(len_written) =>
            len_written == 1
            && data == old(data) + [a]
            // Dafny->Boogie drops an old: https://github.com/dafny-lang/dafny/issues/320
            //&& data[..] == old(data)[.. old(pos)] + [a] + old(data)[old(pos) + 1 ..]
        case Failure(e) => unchanged(`data)
    {
      if 1 <= Capacity() {
        data := data + [a];
        return Success(1);
      } else {
        return Failure("IO Error: Reached end of stream.");
      }
    }
  }
}
