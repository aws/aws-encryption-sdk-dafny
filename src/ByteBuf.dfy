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

  function method ByteBufAdvance(bb: ByteBuf, n: nat): ByteBuf
    requires GoodByteBuf(bb) && n <= bb.len
    ensures GoodByteBuf(ByteBufAdvance(bb, n))
  {
    ByteBuf(bb.a, bb.start + n, bb.end, bb.len - n)
  }

  function method ByteBufFromRemaining(bb: ByteBuf): ByteBuf
    requires GoodByteBuf(bb)
    ensures GoodByteBuf(ByteBufFromRemaining(bb))
  {
    ByteBuf(bb.a, bb.start + bb.len, bb.end, 0)
  }

  function method ByteBufElongate(bb: ByteBuf, n: nat): ByteBuf
    requires GoodByteBuf(bb) && n <= ByteBufRemaining(bb)
    ensures GoodByteBuf(ByteBufElongate(bb, n))
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
    return true, buf.(len := buf.len + len);
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
    return true, ByteBufElongate(bb, 2);
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

  method ByteCursorSplit(bc: ByteCursor, n: nat) returns (success: bool, bc0: ByteCursor, bc1: ByteCursor)  // aws_byte_cursor_advance
    requires GoodByteCursor(bc)
    ensures success ==> GoodByteCursor(bc0) && GoodByteCursor(bc1) && bc0.a == bc1.a == bc.a && ByteCursorAdvances(bc, bc1)
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
}
