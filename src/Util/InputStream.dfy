include "StandardLibrary.dfy"

module M_InputStream {
  import opened StandardLibrary

class InputStream {
    // should be inherited
    ghost var content: seq<byte>
    ghost var Repr: set<object>

    var data: array<byte>;
    var pos: nat;

    predicate Valid()
        reads this, Repr
    {
        this in Repr && 
        data in Repr && 
        pos <= data.Length && 
        data[pos..] == content
    }

    constructor (data: array<byte>) 
        ensures Valid() && fresh(Repr - {this, data})
        ensures this.content == data[..]
    {
        this.content := data[..];
        this.data := data;
        this.pos := 0;
        this.Repr := {this, data};
    }
    
    /*
    method readAll(b: array<byte>) returns (nRead: Either<int, Error>)
        requires Valid()
        requires b !in Repr
        modifies b
        ensures nRead.Left? ==>
          if b.Length == 0 then
            // special case: if provided array is of length 0, read is a NOP
            nRead.left == 0 && b == old(b) && content == old(content)
          else if nRead.left == -1 then
            // EOF case
            content == [] && old(content) == [] && b == old(b)
          else 
            // default case
            1 <= nRead.left <= b.Length &&
            nRead.left <= |old(content)| &&
            content == old(content)[nRead.left..] &&
            b[..nRead.left] == old(content)[..nRead.left]
        ensures Valid() && fresh(Repr - old(Repr))
        
    {
        nRead := read(b, 0, b.Length);
    }
    */
    method {:extern "read"} read(b: array<byte>, off: nat, len: nat) returns (nRead: Either<nat, Error>)
    // TODO: contract
    /*
    method /*{:extern "read"}*/ read(b: array<byte>, off: nat, len: nat) returns (nRead: Either<int, Error>)
        requires Valid()
        requires off <= b.Length
        requires len <= b.Length - off
        requires b !in Repr
        modifies b
        ensures nRead.Left? ==>
          if len == 0 then
            // special case: if provided array is of length 0, read is a NOP
            nRead.left == 0 && unchanged(b) && content == old(content)
          else if nRead.left == -1 then
            // EOF case
            content == [] && old(content) == [] && unchanged(b)
          else 
            // default case
            1 <= nRead.left <= len &&
            nRead.left <= |old(content)| &&
            content == old(content)[nRead.left..] &&
            b[..off] == old(b[..off]) &&
            b[off..off+nRead.left] == old(content)[..nRead.left] &&
            b[off+nRead.left..] == old(b[off+nRead.left..])
        ensures Valid() && fresh(Repr - old(Repr))
    {
        if len == 0 { return Left(0); }        
        if (pos < data.Length) {
            var n := min(data.Length-pos, len);
            forall i | 0 <= i < n {
                b[off+i] := data[pos+i];
            }
            pos := pos + n;
            content := content[n..];
            assert data[pos..] == content;
            nRead := Left(n);
        } else {
            // TODO: should this be an error?
            nRead := Left(-1); // EOF
        }
    }
    */
}

}