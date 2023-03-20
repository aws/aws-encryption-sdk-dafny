namespace aws.cryptography.primitives

@enum([
  {
    name: "PKCS1",
    value: "PKCS1",
  },
  {
    name: "OAEP_SHA1",
    value: "OAEP_SHA1",
  },
  {
    name: "OAEP_SHA256",
    value: "OAEP_SHA256",
  },
  {
    name: "OAEP_SHA384",
    value: "OAEP_SHA384",
  },
  {
    name: "OAEP_SHA512",
    value: "OAEP_SHA512",
  },
])
string RSAPaddingMode

// The smallest ciphertext length is defined using PKCS1, 
// where messageLength <= k - 11,
// where k is defined as the length in octets (bytes) of the modulus n.
// This means that the minimum possible modulus length in bits can be calculated as:
// (x + 7) / 8 - 11 == 0 ==> min x == 81
// (where x is the length of the modulus in bits and messageLength == 0). 
// In practice, this number should be much higher (at least 1024 or, better, 2048).
@range(min: 81)
integer RSAModulusLengthBits

// Our GenerateRSAKeyPair takes in a more constrained version
// of `RSAModulusLengthBits` to prevent an unbounded, expensive
// calculation to generate unreasonably large RSA keys.
// We currently only support a max size of 4096 for key generation.
@range(min: 81, max: 4096)
integer RSAModulusLengthBitsToGenerate

operation GenerateRSAKeyPair {
  input: GenerateRSAKeyPairInput,
  output: GenerateRSAKeyPairOutput,
  errors: [],
}

structure GenerateRSAKeyPairInput {
  @required
  lengthBits: RSAModulusLengthBitsToGenerate
}
structure GenerateRSAKeyPairOutput {
  @required
  publicKey: RSAPublicKey,
  @required
  privateKey: RSAPrivateKey,
}

@readonly
operation GetRSAKeyModulusLength {
  input: GetRSAKeyModulusLengthInput,
  output: GetRSAKeyModulusLengthOutput,
  errors: [], 
}

structure GetRSAKeyModulusLengthInput {
  @required
  publicKey: Blob
}
structure GetRSAKeyModulusLengthOutput {
  @required
  length: RSAModulusLengthBits
}

structure RSAPublicKey {
  @required
  lengthBits: RSAModulusLengthBits,
  @required
  pem: Blob,
}
structure RSAPrivateKey{
  @required
  lengthBits: RSAModulusLengthBits,
  @required
  pem: Blob,
}

operation RSADecrypt {
  input: RSADecryptInput,
  output: RSADecryptOutput,
  errors: [],
}

structure RSADecryptInput {
  @required
  padding: RSAPaddingMode,
  @required
  privateKey: Blob,
  @required
  cipherText: Blob,
}

@aws.polymorph#positional
structure RSADecryptOutput {
  @required
  plaintext: Blob
}

operation RSAEncrypt {
  input: RSAEncryptInput,
  output: RSAEncryptOutput,
  errors: [],
}

structure RSAEncryptInput {
  @required
  padding: RSAPaddingMode,
  @required
  publicKey: Blob,
  @required
  plaintext: Blob
}

@aws.polymorph#positional
structure RSAEncryptOutput {
  @required
  cipherText: Blob
}
