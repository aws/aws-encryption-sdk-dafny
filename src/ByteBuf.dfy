include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "ByteOrder.dfy"

module ByteBuffer {
  import opened StandardLibrary
  import opened Aws
  import ByteOrder

  // ---------- ByteBuf --------------------------------------------------

  // A ByteBuf is a slice of a byte array. Its capacity is the range buffer[start..end] and
  // its contents is buffer[start..start+len].
  datatype ByteBuf = ByteBuf(a: array<byte>, start: nat, end: nat, len: nat)
  function method ByteBufCapacity(bb: ByteBuf): int {
    bb.end - bb.start
  }
  predicate GoodByteBuf(bb: ByteBuf) {
    bb.start <= bb.end <= bb.a.Length &&
    bb.len <= ByteBufCapacity(bb)
  }
  function method ByteBufRemaining(bb: ByteBuf): nat
    requires GoodByteBuf(bb)
  {
    ByteBufCapacity(bb) - bb.len
  }

  predicate ByteBufAdvances(b0: ByteBuf, b1: ByteBuf)
    requires GoodByteBuf(b0)
  {
    GoodByteBuf(b1) &&
    b0.a == b1.a && b0.start == b1.start && b0.end == b1.end &&
    b0.len <= b1.len
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

  function method ByteBufFromRemaining(bb: ByteBuf): ByteBuf
    requires GoodByteBuf(bb)
    ensures GoodByteBuf(ByteBufFromRemaining(bb))
  {
    ByteBuf(bb.a, bb.start + bb.len, bb.end, 0)
  }

  function method ByteBufAdvance(bb: ByteBuf, n: nat): ByteBuf
    requires GoodByteBuf(bb) && n <= ByteBufRemaining(bb)
    ensures GoodByteBuf(ByteBufAdvance(bb, n))
  {
    bb.(len := bb.len + n)
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

  method ByteBufClear(bb: ByteBuf)
    requires GoodByteBuf(bb)
    modifies bb.a
  {
    forall i | bb.start <= i < bb.end {
      bb.a[i] := 0;
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

  /**
   * Write specified number of bytes from array to byte buffer.
   *
   * On success, returns true and updates the buffer length accordingly.
   * If there is insufficient space in the buffer, returns false, leaving the
   * buffer unchanged.
   */
  method ByteBufWrite(buf: ByteBuf, src: array<byte>, len: nat) returns (success: bool, buf': ByteBuf)
    requires GoodByteBuf(buf) && len <= src.Length
    modifies buf.a
    ensures GoodByteBuf(buf')
    ensures !success ==> buf' == buf && unchanged(buf.a)
    ensures success ==> buf' == buf.(len := buf.len + len)
  {
    if ByteBufRemaining(buf) < len {
      return false, buf;
    }
    forall i | 0 <= i < len {
      buf.a[buf.start + buf.len + i] := src[i];
    }
    return true, ByteBufAdvance(buf, len);
  }

  /**
   * Writes a 16-bit integer in network byte order (big endian) to buffer.
   *
   * On success, returns true and updates the cursor /length accordingly.
   * If there is insufficient space in the cursor, returns false, leaving the
   * cursor unchanged.
   */
  method ByteBufWriteBe16(bb: ByteBuf, x: nat) returns (success: bool, bb': ByteBuf)
    requires GoodByteBuf(bb) && x < 0x1_0000
    modifies bb.a
    ensures bb' == if success then bb.(len := bb.len + 2) else bb
  {
    if ByteBufRemaining(bb) < 2 {
      return false, bb;
    }
    var b1, b0 := ByteOrder.ToBytes2(x);
    var n := bb.start + bb.len;
    bb.a[n] := b1;
    bb.a[n + 1] := b0;
    return true, ByteBufAdvance(bb, 2);
  }

  // ---------- ByteCursor --------------------------------------------------

  // A ByteCursor represents a movable pointer within a byte array. It points to "len" bytes
  // starting at position "start" in "a".
  datatype ByteCursor = ByteCursor(a: array<byte>, start: nat, len: nat)
  predicate GoodByteCursor(bc: ByteCursor) {
    bc.start + bc.len <= bc.a.Length
  }

  predicate ByteCursorAdvances(c0: ByteCursor, c1: ByteCursor)
    requires GoodByteCursor(c0)
  {
    GoodByteCursor(c1) &&
    c0.a == c1.a &&
    c0.start <= c1.start &&
    c0.start + c0.len == c1.start + c1.len
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

  function method ByteCursorAdvance(bc: ByteCursor, n: nat): ByteCursor
    requires GoodByteCursor(bc) && n <= bc.len
    ensures ByteCursorAdvances(bc, ByteCursorAdvance(bc, n))
  {
    ByteCursor(bc.a, bc.start + n, bc.len - n)
  }

  function method ByteCursorDifference(orig: ByteCursor, updated: ByteCursor): nat
    requires GoodByteCursor(orig) && GoodByteCursor(updated)
    requires orig.a == updated.a && orig.start <= updated.start <= orig.start + orig.len
  {
    updated.start - orig.start
  }

  method ByteCursorSplit(bc: ByteCursor, n: nat) returns (success: bool, bc0: ByteCursor, bc1: ByteCursor)  // aws_byte_cursor_advance
    requires GoodByteCursor(bc)
    ensures success ==>
      GoodByteCursor(bc0) && bc0.a == bc.a && bc0.start == bc.start && bc0.len == n &&
      ByteCursorAdvances(bc, bc1) && bc1.start == bc.start + n
    ensures !success ==> bc1 == bc
  {
    if n <= bc.len {
      bc0 := bc.(len := n);
      bc1 := bc.(start := bc.start + n, len := bc.len - n);
      success := true;
    } else {
      bc1 := bc;
      success := false;
    }
  }

  method ByteCursorClear(bc: ByteCursor)
    requires GoodByteCursor(bc)
    modifies bc.a
  {
    forall i | 0 <= i < bc.len {
      bc.a[bc.start + i] := 0;
    }
  }

  method ByteCursorReadByte(bc: ByteCursor) returns (success: bool, bc': ByteCursor, b: byte)
    requires GoodByteCursor(bc)
    ensures success ==> ByteCursorAdvances(bc, bc')
    ensures !success ==> bc' == bc
  {
    if bc.len == 0 {
      return false, bc, 0;
    }
    b := bc.a[bc.start];
    bc' := bc.(start := bc.start + 1, len := bc.len - 1);
    success := true;
  }

  method ByteCursorReadBe16(bc: ByteCursor) returns (success: bool, bc': ByteCursor, x: nat)
    requires GoodByteCursor(bc)
    ensures success ==> ByteCursorAdvances(bc, bc') && x < 0x1_0000
    ensures !success ==> bc' == bc
  {
    if bc.len < 2 {
      return false, bc, 0;
    }
    var b0 := bc.a[bc.start];
    var b1 := bc.a[bc.start + 1];
    x := 256 * b1 as int + b0 as int;
    bc' := bc.(start := bc.start + 2, len := bc.len - 2);
    success := true;
  }

  method ByteCursorReadBe32(bc: ByteCursor) returns (success: bool, bc': ByteCursor, x: nat)
    requires GoodByteCursor(bc)
    ensures success ==> ByteCursorAdvances(bc, bc') && x < 0x1_0000_0000
    ensures !success ==> bc' == bc
  {
    if bc.len < 4 {
      return false, bc, 0;
    }
    var b0 := bc.a[bc.start];
    var b1 := bc.a[bc.start + 1];
    var b2 := bc.a[bc.start + 2];
    var b3 := bc.a[bc.start + 3];
    x := 0x100_0000 * b3 as int + 0x1_0000 * b2 as int + 0x100 * b1 as int + b0 as int;
    bc' := bc.(start := bc.start + 4, len := bc.len - 4);
    success := true;
  }


  method ByteCursorReadIntoArray(source: ByteCursor, dest: array<byte>, destOffset: nat, n: nat) returns (success: bool, source': ByteCursor)
    requires GoodByteCursor(source)
    requires destOffset + n <= dest.Length
    modifies dest
    ensures success ==> ByteCursorAdvances(source, source')
    ensures !success ==> source == source' && unchanged(dest)
  {
    if source.len < n {
      return false, source;
    }
    forall i | 0 <= i < n {
      dest[destOffset + i] := source.a[source.start + i];
    }
    source' := ByteCursorAdvance(source, n);
    success := true;
  }

  method ByteCursorReadIntoByteBuf(source: ByteCursor, dest: ByteBuf) returns (success: bool, source': ByteCursor, dest': ByteBuf)
    requires GoodByteCursor(source) && GoodByteBuf(dest)
    modifies dest.a
    ensures success ==> ByteCursorAdvances(source, source') && ByteBufAdvances(dest, dest')
    ensures !success ==> source == source' && dest == dest' && unchanged(dest.a)
  {
    var n := ByteBufRemaining(dest);
    success, source' := ByteCursorReadIntoArray(source, dest.a, dest.start + dest.len, n);
    if success {
      dest' := ByteBufAdvance(dest, n);
      assert ByteBufRemaining(dest') == 0;
    } else {
      dest' := dest;
    }
  }

  method ByteCursorRead(source: ByteCursor, n: nat) returns (source': ByteCursor, a: array?<byte>)
    requires GoodByteCursor(source)
    ensures a != null ==> ByteCursorAdvances(source, source') && fresh(a)
    ensures a == null ==> source == source'
  {
    a := new byte[n];
    var success;
    success, source' := ByteCursorReadIntoArray(source, a, 0, n);
    if !success {
      return source, null;
    }
  }
}
