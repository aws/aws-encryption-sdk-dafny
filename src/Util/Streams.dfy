include "../StandardLibrary/StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  trait Stream {

    ghost var Repr : set<object>
    predicate Valid() reads this
    function method capacity()  : nat reads this requires Valid() // An upper bound on the amount of data the stream can accept on Write
    function method available() : nat reads this requires Valid() // An upper bound on the amount of data the stream can deliver on Read


    method Write(a : array<uint8>, off : nat, req : nat) returns (res : Result<nat>)
      requires Valid()
      requires a.Length >= off + req
      modifies Repr
      requires a !in Repr
      ensures Valid()
      ensures
        match res
          case Success(len_written) => len_written == min(req, old(capacity()))
          case Failure(e) => true


    method Read(i : array<uint8>, off : nat, req : nat) returns (res : Result<nat>)
      requires Valid()
      requires i.Length >= off + req
      requires i !in Repr
      modifies i, this
      ensures Valid()
      ensures
        match res
          case Success(len_read) => len_read == min(req, old(available()))
          case Failure(e) => true
  }


  class StringReader extends Stream {

    var data : array<uint8>
    var pos : nat

    predicate Valid() reads this {
      this in Repr &&
      data in Repr &&
      pos <= data.Length
    }

    function method capacity() : nat reads this requires Valid() { 0 }
    function method available() : nat reads this requires Valid() { data.Length - pos }


    constructor(d : array<uint8>)
      ensures Valid()
    {
        Repr := {this, d};
        data := d;
        pos := 0;
    }

    method Write(a : array<uint8>, off : nat, req : nat) returns (res : Result<nat>)
      requires Valid()
      modifies this
      requires a !in Repr
      ensures Valid()
      ensures
        match res
          case Success(len_written) => len_written == min(req, old(capacity()))
          case Failure(e) => unchanged(this)
    {
      res := Failure("IO Error: Cannot write to StringReader");
    }

    method Read(arr : array<uint8>, off : nat, req : nat) returns (res : Result<nat>)
      requires Valid()
      requires arr.Length >= off + req
      requires arr != data
      ensures Valid()
      modifies arr, this
      ensures unchanged(`data)
      ensures var n := min(req, old(available()));
        arr[..] == arr[..off] + data[old(pos) .. (old(pos) + n)] + arr[off + n ..]
      ensures
        match res
          case Success(len_read) => len_read == min(req, old(available()))
          case Failure(e) => unchanged(this) && unchanged(arr)
    {
      if off == arr.Length || available() == 0 {
        assert (min (req, available())) == 0;
        res := Success(0);
      }
      else {
        var n := min(req, available());
        forall i | 0 <= i < n {
          arr[off + i] := data[pos + i];
        }
        pos := pos + n;
        res := Success(n);
      }
    }
    /*
    // TODO add a version without arrays
    method ReadSimple(arr: array<uint8>) returns (res: Result<nat>)
      requires Valid()
      ensures Valid()
      modifies this
      ensures
        match res
          case Success(len_read) =>
            var n := arr.Length;
            && pos == old(pos) + n
            && arr[..] == data[old(pos) .. pos]
            && len_read == n
          case Failure(e) => unchanged(this)
    {
      if arr.Length <= available() {
        forall i | 0 <= i < arr.Length {
          arr[i] := data[pos + i];
        }
        pos := pos + arr.Length;
        res := Success(arr.Length);
      } else {
        res := Failure("IO Error: Not enough bytes available on stream.");
      }
    }
    */
  }

  class StringWriter extends Stream {
    ghost var data : seq<uint8>

    predicate Valid()
      reads this
    {
      this in Repr
    }

    function method capacity(): nat
      reads this
      requires Valid()
      {
        0 // TODO?
      }

    function method available(): nat
      reads this
      requires Valid()
      {
        0 // TODO
      }

    constructor(n : nat)
      ensures Valid()
    {
        data := [];
        Repr := {this};
    }

    method Write(a: array<uint8>, off: nat, req: nat) returns (res: Result<nat>)
      requires Valid()
      requires off + req <= a.Length
      requires a !in Repr
      modifies `data
      ensures unchanged(`Repr)
      ensures Valid()
      ensures
        match res
          case Success(len_written) =>
            if old(capacity()) == 0
            then
              len_written == 0
            else
              //&& old(pos + n < |data|)
              //&& Written(old(data), data, old(pos), pos, a[off..off+n], len_written, n)
              && len_written == min(req, old(capacity()))
              && data == old(data) + a[off..off+req]
          case Failure(e) => true
    {
      if off == a.Length || capacity() == 0 {
        res := Success(0);
      }
      else {
        var n := min(req, capacity());
        data := data + a[off..off+req];
        res := Success(n);
      }
    }

    method WriteSimple(a: array<uint8>) returns (res: Result<nat>)
      requires Valid()
      requires a !in Repr
      modifies `data
      ensures unchanged(`Repr)
      ensures unchanged(a)
      ensures Valid()
      ensures
        match res
          case Success(len_written) =>
              && len_written == a.Length
              && data[..] == old(data) + a[..]
          case Failure(e) => unchanged(`data)
    {
      if a.Length <= capacity() {
        data := data + a[..];
        res := Success(a.Length);
      } else {
        res := Failure("IO Error: Reached end of stream.");
      }
    }

    method WriteSimpleSeq(a: seq<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures unchanged(`Repr)
      ensures Valid()
      ensures
        match res
          case Success(len_written) =>
              && len_written == |a|
              && data[..] == old(data) + a
          case Failure(e) => unchanged(`data)
    {
      if |a| <= capacity() {
        data := data + a;
        res := Success(|a|);
      } else {
        res := Failure("IO Error: Reached end of stream.");
      }
    }

    method WriteSingleByte(a: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures unchanged(`Repr)
      ensures Valid()
      ensures
        match res
          case Success(len_written) =>
            if old(capacity()) == 0
            then
              len_written == 0
            else
              && len_written == 1
              && data == old(data) + [a]
              // Dafny->Boogie drops an old: https://github.com/dafny-lang/dafny/issues/320
              //&& data[..] == old(data)[.. old(pos)] + [a] + old(data)[old(pos) + 1 ..]
          case Failure(e) => unchanged(`data)
    {
      if capacity() == 0 {
        res := Success(0);
      }
      else {
        data := data + [a];
        res := Success(1);
      }
    }

    method WriteSingleByteSimple(a: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures unchanged(`Repr)
      ensures Valid()
      ensures
        match res
          case Success(len_written) =>
              len_written == 1
              && data == old(data) + [a]
              // Dafny->Boogie drops an old: https://github.com/dafny-lang/dafny/issues/320
              //&& data[..] == old(data)[.. old(pos)] + [a] + old(data)[old(pos) + 1 ..]
          case Failure(e) => unchanged(`data)
    {
      if 1 <= capacity() {
        data := data + [a];
        res := Success(1);
      } else {
        res := Failure("IO Error: Reached end of stream.");
      }
    }

    method Read(arr : array<uint8>, off : nat, req : nat) returns (res : Result<nat>)
      requires Valid()
      requires arr.Length >= off + req
      ensures Valid()
      modifies arr, this
      ensures
        match res
          case Success(len_read) => len_read == min(req, old(available()))
          case Failure(e) => unchanged(this) && unchanged(arr)
    {
      res := Failure("IO Error: Cannot read from StringWriter");
    }
  }

}
