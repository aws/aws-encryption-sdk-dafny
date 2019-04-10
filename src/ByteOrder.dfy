include "StandardLibrary.dfy"

module ByteOrder {
  import opened StandardLibrary

  method ToBytes2(x: nat) returns (b1: byte, b0: byte)
    requires x < 0x1_0000
  {
    b1 := (x / 256) as byte;
    b0 := (x % 256) as byte;
  }

  method ToBytes4(x: nat) returns (b3: byte, b2: byte, b1: byte, b0: byte)
    requires x < 0x1_0000_0000
  {
    var y;
    b0, y := (x % 256) as byte, x / 256;
    b1, y := (y % 256) as byte, y / 256;
    b2, y := (y % 256) as byte, y / 256;
    b3    := (y % 256) as byte;
  }
}
