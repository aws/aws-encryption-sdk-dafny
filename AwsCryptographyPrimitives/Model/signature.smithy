namespace aws.cryptography.primitives

@enum([
  {
    name: "ECDSA_P384",
    value: "ECDSA_P384",
  },
  {
    name: "ECDSA_P256",
    value: "ECDSA_P256",
  },
])
string ECDSASignatureAlgorithm

operation GenerateECDSASignatureKey {
  input: GenerateECDSASignatureKeyInput,
  output: GenerateECDSASignatureKeyOutput,
  errors: []
}
operation ECDSASign {
  input: ECDSASignInput,
  output: ECDSASignOutput,
  errors: []
}
operation ECDSAVerify {
  input: ECDSAVerifyInput,
  output: ECDSAVerifyOutput,
  errors: []
}

structure GenerateECDSASignatureKeyInput {
  @required
  signatureAlgorithm: ECDSASignatureAlgorithm
}

structure GenerateECDSASignatureKeyOutput {
  @required
  signatureAlgorithm: ECDSASignatureAlgorithm,
  @required
  verificationKey: Blob,
  @required
  signingKey: Blob
}

structure ECDSASignInput {
  @required
  signatureAlgorithm: ECDSASignatureAlgorithm,
  @required
  signingKey: Blob,
  @required
  message: Blob
}

@aws.polymorph#positional
structure ECDSASignOutput {
  @required
  signature: Blob
}

structure ECDSAVerifyInput {
  @required
  signatureAlgorithm: ECDSASignatureAlgorithm,
  @required
  verificationKey: Blob,
  @required
  message: Blob,
  @required
  signature: Blob,
}

@aws.polymorph#positional
structure ECDSAVerifyOutput {
  @required
  success: Boolean,
}

