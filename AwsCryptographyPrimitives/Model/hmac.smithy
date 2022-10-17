namespace aws.cryptography.primitives

operation HMac {
  input: HMacInput,
  output: HMacOutput,
}

structure HMacInput {
  @required
  digestAlgorithm: DigestAlgorithm,
  @required
  key: Blob,
  @required
  message: Blob,
}

@aws.polymorph#positional
structure HMacOutput {
  digest: Blob
}
