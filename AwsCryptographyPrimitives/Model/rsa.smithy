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
// where messageLength <= k - 11 and k represents the strength,
// defined as the length in octets (bytes) of the modulus n.
// This means that the minimum possible strength in bits can be calculated as:
// (strength + 7) / 8 - 11 == 0 ==> min strength == 81 in this scenario (where messageLength == 0). 
// In practice, this number should be much higher (at least 1024 or, better, 2048).
// TODO: Determine if we want to enforce a min value of 2048 bits as the min strength (requires updating the spec)
// TODO: Determine if we want to enforce a max value of x as the max strength
@range(min: 81, max: 4096)
integer RSAStrengthBits


operation GenerateRSAKeyPair {
  input: GenerateRSAKeyPairInput,
  output: GenerateRSAKeyPairOutput,
  errors: [],
}

structure GenerateRSAKeyPairInput {
  @required
  strength: RSAStrengthBits
}
structure GenerateRSAKeyPairOutput {
  @required
  publicKey: RSAPublicKey,
  @required
  privateKey: RSAPrivateKey,
}

structure RSAPublicKey {
  @required
  strength: RSAStrengthBits,
  @required
  pem: Blob,
}
structure RSAPrivateKey{
  @required
  strength: RSAStrengthBits,
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
