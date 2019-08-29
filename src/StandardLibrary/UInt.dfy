module {:extern "STLUINT"} StandardLibrary.UInt {
  const UINT8_LIMIT := 256
  newtype UInt8 = x | 0 <= x < UINT8_LIMIT
  
  const UINT16_LIMIT := 0x1_0000
  newtype UInt16 = x | 0 <= x < UINT16_LIMIT

  const UINT32_LIMIT := 0x1_0000_0000
  newtype UInt32 = x | 0 <= x < UINT32_LIMIT

  const UINT64_LIMIT := 0x1_0000_0000_0000_0000
  newtype UInt64 = x | 0 <= x < UINT64_LIMIT
}
