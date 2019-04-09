include "StandardLibrary.dfy"
include "AwsCrypto.dfy"

module ByteBuffer {
  import opened StandardLibrary
  import opened Aws

  // A ByteBuf is a slice of a byte array. Its capacity is the range buffer[start..end] and
  // its contents is buffer[start..start+len].
  datatype ByteBuf = ByteBuf(a: array<byte>, start: nat, end: nat, len: nat)
  function ByteBufCapacity(bb: ByteBuf): int {
    bb.end - bb.start
  }
  predicate GoodByteBuf(bb: ByteBuf) {
    bb.start <= bb.end <= bb.a.Length &&
    bb.len <= ByteBufCapacity(bb)
  }

  // A ByteCursor represents a movable pointer within a byte array. It points to "len" bytes
  // starting at position "start" in "a".
  datatype ByteCursor = ByteCursor(a: array<byte>, start: nat, len: nat)
  predicate GoodByteCursor(bc: ByteCursor) {
    bc.start + bc.len <= bc.a.Length
  }

  method ByteBufInit(capacity: nat) returns (bb: ByteBuf)
    ensures fresh(bb.a) && GoodByteBuf(bb) && ByteBufCapacity(bb) == capacity && bb.len == 0
  {
    var a := new byte[capacity];
    bb := ByteBuf(a, 0, capacity, 0);
  }

  method ByteBufInit_Full(capacity: nat) returns (bb: ByteBuf)
    ensures fresh(bb.a) && GoodByteBuf(bb) && ByteBufCapacity(bb) == capacity == bb.len
  {
    var a := new byte[capacity];
    bb := ByteBuf(a, 0, capacity, capacity);
  }

  method ByteBufInit_Full_AllZero(capacity: nat) returns (bb: ByteBuf)
    ensures fresh(bb.a) && GoodByteBuf(bb) && ByteBufCapacity(bb) == capacity == bb.len
    ensures forall i :: bb.start <= i < bb.start + bb.len ==> bb.a[i] == 0
  {
    var a := new byte[capacity];
    forall i | 0 <= i < capacity {
      a[i] := 0;
    }
    bb := ByteBuf(a, 0, capacity, capacity);
  }

  function method ByteBufFromArray(a: array<byte>, len: nat): ByteBuf
    requires len <= a.Length
    ensures GoodByteBuf(ByteBufFromArray(a, len))
  {
    ByteBuf(a, 0, len, len)
  }

  function method ByteBufFromEmptyArray(a: array<byte>, capacity: nat): ByteBuf
    requires capacity <= a.Length
    ensures GoodByteBuf(ByteBufFromEmptyArray(a, capacity))
  {
    ByteBuf(a, 0, capacity, 0)
  }

  method ByteBufFill(bb: ByteBuf, b: byte)
    requires GoodByteBuf(bb)
    modifies bb.a
    ensures forall i :: bb.start <= i < bb.start + bb.len ==> bb.a[i] == b
    ensures forall i :: 0 <= i < bb.start || bb.start + bb.len <= i < bb.a.Length ==> bb.a[i] == old(bb.a[i])
  {
    forall i | 0 <= i < bb.len {
      bb.a[bb.start + i] := b;
    }
  }

  method ByteBufCopyFromByteBuf(dest: ByteBuf, src: ByteBuf)
    requires GoodByteBuf(dest) && GoodByteBuf(src)
    requires dest.len <= src.len
    modifies dest.a
  {
    forall i | 0 <= i < dest.len {
      dest.a[dest.start + i] := src.a[src.start + i];
    }
  }

  method ByteBufCopyFromByteBufOffset(dest: ByteBuf, src: ByteBuf, srcOffset: nat)
    requires GoodByteBuf(dest) && GoodByteBuf(src)
    requires dest.len <= src.len - srcOffset
    modifies dest.a
  {
    forall i | 0 <= i < dest.len {
      dest.a[dest.start + i] := src.a[src.start + srcOffset + i];
    }
  }

  function method ByteCursorFromBuf(bb: ByteBuf): ByteCursor
    requires GoodByteBuf(bb)
    ensures GoodByteCursor(ByteCursorFromBuf(bb))
  {
    ByteCursor(bb.a, bb.start, bb.len)
  }
  
  function method ByteCursorFromArray(a: array<byte>, len: nat): ByteCursor
    requires len <= a.Length
    ensures GoodByteCursor(ByteCursorFromArray(a, len))
  {
    ByteCursor(a, 0, len)
  }

  function method ByteCursorAdvance(bc: ByteCursor, n: nat): (bool, ByteCursor)
    requires GoodByteCursor(bc)
    ensures var (success, bc') := ByteCursorAdvance(bc, n);
      GoodByteCursor(bc')
  {
    var max := UINT64_MAX / 2;
    if n <= max && n <= bc.len <= max then
      var bc' := ByteCursor(bc.a, bc.start + n, bc.len - n);
      (true, bc')
    else
      (false, bc)
  }
}
