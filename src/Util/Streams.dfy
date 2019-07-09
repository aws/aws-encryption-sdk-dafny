include "StandardLibrary.dfy"

module Streams {
  import opened StandardLibrary

  trait Stream {

    ghost var Repr : set<object>
    predicate Valid() reads this
    function method capacity() : nat reads this requires Valid() // An upper bound on the amount of data the stream can accept on Write
    function method available() : nat reads this requires Valid() // An upper bound on the amount of data the stream can deliver on Read


    method Write(a : array<byte>, off : nat, req : nat) returns (len_written : Either<nat, Error>)
      requires Valid()
      requires a.Length >= off + req
      modifies Repr
      requires a !in Repr
      ensures len_written.Left? ==> len_written.left == min(req, old(capacity()))
      ensures len_written.Right? ==> unchanged(this)
      ensures Valid()


    method Read(i : array<byte>, off : nat, req : nat) returns (len_read : Either<nat, Error>)
      requires Valid()
      requires i.Length >= off + req
      requires i !in Repr
      modifies i, this
      ensures Valid()
      ensures len_read.Left? ==> len_read.left == min(req, old(available())) 
      ensures len_read.Right? ==> unchanged(this)
  }


  class StringReader extends Stream {

    var data : array<byte>
    var pos : nat

    predicate Valid() reads this {
      this in Repr &&
      data in Repr &&
      pos <= data.Length
    }

    function method capacity() : nat reads this requires Valid() { 0 }
    function method available() : nat reads this requires Valid() { data.Length - pos }


    constructor(d : array<byte>)
      ensures Valid()
    {
        Repr := {this, d};
        data := d;
        pos := 0;
    }

    method Write(a : array<byte>, off : nat, req : nat) returns (len_written : Either<nat, Error>)
      requires Valid()
      modifies this
      requires a !in Repr
      ensures len_written.Left? ==> len_written.left == min(req, old(capacity()))
      ensures len_written.Right? ==> unchanged(this)
      ensures Valid()
      ensures len_written.Right?
    {
      len_written := Right(IOError("Cannot write to StringReader"));
    }
    
    method Read(arr : array<byte>, off : nat, req : nat) returns (len_read : Either<nat, Error>)
      requires Valid()
      requires arr.Length >= off + req
      requires arr != data
      ensures Valid()
      modifies arr, this
      ensures len_read.Left? ==> len_read.left == min(req, old(available())) 
      ensures len_read.Right? ==> unchanged(this) && unchanged(arr)
      ensures unchanged(`data)
      ensures var n := min(req, old(available()));
        arr[..] == arr[..off] + data[old(pos) .. (old(pos) + n)] + arr[off + n ..]
      ensures len_read.Left?
    {
      if off == arr.Length || available() == 0 {
        assert (min (req, available())) == 0;
        len_read := Left(0);
      }
      else {
        var n := min(req, available());
        forall i | 0 <= i < n {
          arr[off + i] := data[pos + i];
        }
        pos := pos + n;
        len_read := Left(n);
      }
    }
  }

  class StringWriter extends Stream {
    var data : array<byte>
    var pos : nat

    predicate Valid() reads this {
      this in Repr &&
      data in Repr &&
      pos <= data.Length 
    }

    function method capacity() : nat reads this requires Valid() { data.Length - pos }
    function method available() : nat reads this requires Valid() { 0 }


    constructor(n : nat)
      ensures Valid()
    {
        data := new byte[n];
        Repr := {this, data};
        pos := 0;
    }

    method Write(a : array<byte>, off : nat, req : nat) returns (len_written : Either<nat, Error>)
      requires Valid()
      requires a.Length >= off + req
      modifies this, data
      requires a !in Repr
      ensures len_written.Left? ==> len_written.left == min(req, old(capacity()))
      ensures len_written.Right? ==> unchanged(this)
      ensures Valid()
      ensures unchanged(`data)
      ensures var n := min(req, old(capacity()));
        data[..] == old(data)[..old(pos)] + a[off .. off + n] + old(data)[old(pos) + n ..]
      ensures len_written.Left?
    {
      if off == a.Length || capacity() == 0 {
        len_written := Left(0);
      }
      else {
        var n := min(req, capacity());
        forall i | 0 <= i < min(req, capacity()) {
          data[pos + i] := a[off + i];
        }
        len_written := Left(n);
        pos := pos + n;

      }
    }
    
    method Read(arr : array<byte>, off : nat, req : nat) returns (len_read : Either<nat, Error>)
      requires Valid()
      requires arr.Length >= off + req
      requires arr != data
      ensures Valid()
      modifies arr, this
      ensures len_read.Left? ==> len_read.left == min(req, old(available())) 
      ensures len_read.Right? ==> unchanged(this) && unchanged(arr)
      ensures len_read.Right?
    {
      len_read := Right(IOError("Cannot read from StringWriter"));
    }
  }

}
