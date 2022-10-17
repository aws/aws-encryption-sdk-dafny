namespace aws.cryptography.primitives

@range(min: 1, max: 32)
integer SymmetricKeyLength
@range(min: 0, max: 255)
integer Uint8Bits
@range(min: 0, max: 32)
integer Uint8Bytes

operation AESEncrypt {
  input: AESEncryptInput,
  output: AESEncryptOutput,
  errors: []
}
operation AESDecrypt {
  input: AESDecryptInput,
  output: AESDecryptOutput,
  errors: []
}

structure AESEncryptInput {
  @required
  encAlg: AES_GCM,
  @required
  iv: Blob,
  @required
  key: Blob,
  @required
  msg: Blob,
  @required
  aad: Blob
}

structure AESEncryptOutput {
  @required
  cipherText: Blob,
  @required
  authTag: Blob
}

structure AESDecryptInput {
  @required
  encAlg: AES_GCM,
  @required
  key: Blob,
  @required
  cipherTxt: Blob,
  @required
  authTag: Blob,
  @required
  iv: Blob,
  @required
  aad: Blob
}

@aws.polymorph#positional
structure AESDecryptOutput {
  plaintext: Blob
}

structure AES_GCM {
  @required
  keyLength: SymmetricKeyLength,
  @required
  tagLength: Uint8Bytes,
  @required
  ivLength: Uint8Bits
}
