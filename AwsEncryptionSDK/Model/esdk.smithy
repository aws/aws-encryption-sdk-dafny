namespace aws.encryptionSdk

/////////////
// ESDK Client Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
@aws.polymorph#localService(
  sdkId: "ESDK",
  config: AwsEncryptionSdkConfig,
)
service AwsEncryptionSdk {
  version: "2020-10-24",
  operations: [Encrypt, Decrypt],
  errors: [AwsEncryptionSdkException],
}

@range(min: 1)
long CountingNumbers

// This ESDK does *not* support a frame length of 0
// because 0 is used to designate unframed
// min: 1, max: 2^32
@range(min: 1, max: 4294967296)
long FrameLength

structure AwsEncryptionSdkConfig {
  commitmentPolicy: aws.cryptography.materialProviders#ESDKCommitmentPolicy,
  maxEncryptedDataKeys: CountingNumbers,
}

/////////////
// ESDK Operations

operation Encrypt {
  input: EncryptInput,
  output: EncryptOutput,
}

structure EncryptInput {
  @required
  plaintext: Blob,

  encryptionContext: aws.cryptography.materialProviders#EncryptionContext,

  // One of keyring or CMM are required
  materialsManager: aws.cryptography.materialProviders#CryptographicMaterialsManagerReference,
  keyring: aws.cryptography.materialProviders#KeyringReference,

  algorithmSuiteId: aws.cryptography.materialProviders#ESDKAlgorithmSuiteId,

  frameLength: FrameLength
}

structure EncryptOutput {
  @required
  ciphertext: Blob,

  @required
  encryptionContext: aws.cryptography.materialProviders#EncryptionContext,

  @required
  algorithmSuiteId: aws.cryptography.materialProviders#ESDKAlgorithmSuiteId,
}

operation Decrypt {
  input: DecryptInput,
  output: DecryptOutput,
  errors: [AwsEncryptionSdkException],
}

structure DecryptInput {
  @required
  ciphertext: Blob,

  // One of keyring or CMM are required
  materialsManager: aws.cryptography.materialProviders#CryptographicMaterialsManagerReference,
  keyring: aws.cryptography.materialProviders#KeyringReference,
}

structure DecryptOutput {
  @required
  plaintext: Blob,

  @required
  encryptionContext: aws.cryptography.materialProviders#EncryptionContext,

  @required
  algorithmSuiteId: aws.cryptography.materialProviders#ESDKAlgorithmSuiteId,

  // The spec says that decrypt SHOULD also return the parsed
  // header. We're omitting this for now, until we can spend
  // some more time figuring out what it looks like to model
  // the message format and message header in Smithy.
}

/////////////
// Errors

@error("client")
structure AwsEncryptionSdkException {
  @required
  message: String,
}

@aws.polymorph#reference(service: aws.cryptography.primitives#AwsCryptographicPrimitives)
structure AtomicPrimitivesReference {}

@aws.polymorph#reference(service: aws.cryptography.materialProviders#AwsCryptographicMaterialProviders)
structure MaterialProvidersReference {}
