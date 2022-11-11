namespace aws.cryptography.primitives

operation GenerateRandomBytes {
  input: GenerateRandomBytesInput,
  output: GenerateRandomBytesOutput,
  errors: []
}

structure GenerateRandomBytesInput {
  @required
  length: PositiveInteger
}

@aws.polymorph#positional
structure GenerateRandomBytesOutput {
  @required
  data: Blob
}
