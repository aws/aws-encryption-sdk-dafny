namespace aws.cryptography.primitives

// Key-Derivation Function in Counter Mode
// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-108r1.pdf
operation KdfCounterMode {
  input: KdfCtrInput,
  output: KdfCtrOutput
}

// AES in Counter Mode Operation
// used only as a Key-Derivation Function
operation AesKdfCounterMode {
  input: AesKdfCtrInput,
  output: AesKdfCtrOutput
}

structure KdfCtrInput {
  @required
  ikm: Blob,
  @required
  expectedLength: PositiveInteger,
  nonce: Blob
}

@aws.polymorph#positional
structure KdfCtrOutput {
  @required
  okm: Blob
}

structure AesKdfCtrInput {
  @required
  alg: AES_CTR,
  @required
  ikm: Blob,
  @required
  expectedLength: PositiveInteger,
  nonce: Blob
}

@aws.polymorph#positional
structure AesKdfCtrOutput {
  @required
  okm: Blob
}

structure AES_CTR {
  @required
  keyLength: SymmetricKeyLength,
  @required
  nonceLength: Uint8Bits
}
