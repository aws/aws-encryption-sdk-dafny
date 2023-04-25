namespace aws.cryptography.primitives

@enum([
  {
    name: "SHA_512",
    value: "SHA_512",
  },
  {
    name: "SHA_384",
    value: "SHA_384",
  },
  {
    name: "SHA_256",
    value: "SHA_256",
  },
])
string DigestAlgorithm

operation Digest {
  input: DigestInput,
  output: DigestOutput,
  errors: []
}

structure DigestInput {
  @required
  digestAlgorithm: DigestAlgorithm,
  @required
  message: Blob
}

@aws.polymorph#positional
structure DigestOutput {
  @required
  digest: Blob
}

