namespace aws.cryptography.primitives

@readonly
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
  @required
  digest: Blob
}
