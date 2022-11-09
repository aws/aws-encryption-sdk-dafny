namespace aws.cryptography.materialProviders

@readonly
operation InitializeEncryptionMaterials {
  input: InitializeEncryptionMaterialsInput,
  output: EncryptionMaterials,
}

@readonly
operation InitializeDecryptionMaterials {
  input: InitializeDecryptionMaterialsInput,
  output: DecryptionMaterials,
}

structure InitializeEncryptionMaterialsInput {
  @required
  algorithmSuiteId: AlgorithmSuiteId,

  @required
  encryptionContext: EncryptionContext,

  signingKey: Secret,

  verificationKey: Secret,
}

structure InitializeDecryptionMaterialsInput {
  @required
  algorithmSuiteId: AlgorithmSuiteId,

  @required
  encryptionContext: EncryptionContext,
}

@readonly
operation ValidEncryptionMaterialsTransition {
  input: ValidEncryptionMaterialsTransitionInput,
  errors: [InvalidEncryptionMaterialsTransition]
}

@readonly
operation ValidDecryptionMaterialsTransition {
  input: ValidDecryptionMaterialsTransitionInput,
  errors: [InvalidDecryptionMaterialsTransition]
}

structure ValidEncryptionMaterialsTransitionInput {
  @required
  start: EncryptionMaterials,
  @required
  stop: EncryptionMaterials,
}

structure ValidDecryptionMaterialsTransitionInput {
  @required
  start: DecryptionMaterials,
  @required
  stop: DecryptionMaterials,
}

@error("client")
structure InvalidEncryptionMaterialsTransition {
  @required
  message: String,
}
@error("client")
structure InvalidDecryptionMaterialsTransition {
  @required
  message: String,
}

@readonly
operation EncryptionMaterialsHasPlaintextDataKey {
  input: EncryptionMaterials,
  errors: [InvalidEncryptionMaterials],
}

@readonly
operation DecryptionMaterialsWithPlaintextDataKey {
  input: DecryptionMaterials,
  errors: [InvalidDecryptionMaterials],
}

@error("client")
structure InvalidEncryptionMaterials {
  @required
  message: String,
}
@error("client")
structure InvalidDecryptionMaterials {
  @required
  message: String,
}
