module StandardLibrary.UInt {
  newtype UInt8 = x | 0 <= x < 256

  newtype UInt16 = x | 0 <= x < 0x1_0000
  const UINT16_MAX := 0x1_0000 - 1

  newtype UInt32 = x | 0 <= x < 0x1_0000_0000
  const UINT32_MAX := 0x1_0000_0000 - 1

  newtype UInt64 = x | 0 <= x < 0x1_0000_0000_0000_0000
}