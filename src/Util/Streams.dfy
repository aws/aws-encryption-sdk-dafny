include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait Stream {
    ghost var Repr: set<object>

    predicate Valid()
      reads this

    function method Capacity(): nat  // An upper bound on the amount of data the stream can accept on Write
      requires Valid()
      reads this

    function method Available(): nat  // An upper bound on the amount of data the stream can deliver on Read
      requires Valid()
      reads this

    method Write(a: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && a !in Repr
      requires off + req <= a.Length
      modifies Repr
      ensures Valid()
      ensures match res
        case Success(len_written) => len_written == min(req, old(Capacity()))
        case Failure(e) => true

    method Read(i: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && i !in Repr
      requires off + req <= i.Length
      modifies this, i
      ensures Valid()
      ensures match res
        case Success(len_read) => len_read == min(req, old(Available()))
        case Failure(e) => true
  }


  class StringReader extends Stream {
    var data: array<uint8>
    var pos: nat

    predicate Valid()
      reads this
    {
      this in Repr &&
      data in Repr &&
      pos <= data.Length
    }

    function method Capacity(): nat
      requires Valid()
      reads this
    {
      0
    }

    function method Available(): nat
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

    method Write(a: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && a !in Repr
      modifies this
      ensures Valid()
      ensures match res
        case Success(len_written) => len_written == min(req, old(Capacity()))
        case Failure(e) => unchanged(this)
    {
      return Failure("IO Error: Cannot write to StringReader");
    }

    method Read(arr: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid() && arr != data
      requires off + req <= arr.Length
      modifies this, arr
      ensures Valid()
      ensures unchanged(`data)
      ensures var n := min(req, old(Available()));
        arr[..] == arr[..off] + data[old(pos) .. (old(pos) + n)] + arr[off + n ..]
      ensures match res
        case Success(len_read) => len_read == min(req, old(Available()))
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

    /*
    // TODO add a version without arrays
    method ReadSimple(arr: array<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures  match res
        case Success(len_read) =>
          var n := arr.Length;
          && pos == old(pos) + n
          && arr[..] == data[old(pos) .. pos]
          && len_read == n
        case Failure(e) => unchanged(this)
    {
      if arr.Length <= Available() {
        forall i | 0 <= i < arr.Length {
          arr[i] := data[pos + i];
        }
        pos := pos + arr.Length;
        return Success(arr.Length);
      } else {
        return Failure("IO Error: Not enough bytes available on stream.");
      }
    }
    */
  }

  class StringWriter extends Stream {
    ghost var data: seq<uint8>

    predicate Valid()
      reads this
    {
      this in Repr
    }

    function method Capacity(): nat
      requires Valid()
      reads this
    {
      0 // TODO?
    }

    function method Available(): nat
      requires Valid()
      reads this
    {
      0 // TODO
    }

    constructor(n: nat)
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
            //&& old(pos + n < |data|)
            //&& Written(old(data), data, old(pos), pos, a[off..off+n], len_written, n)
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

    method Read(arr: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid()
      requires off + req <= arr.Length
      modifies this, arr
      ensures Valid()
      ensures match res
        case Success(len_read) => len_read == min(req, old(Available()))
        case Failure(e) => unchanged(this) && unchanged(arr)
    {
      return Failure("IO Error: Cannot read from StringWriter");
    }
  }
}
