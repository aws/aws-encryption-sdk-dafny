namespace aws.encryptionSdk

use aws.encryptionSdk.core#KeyringReference
use aws.encryptionSdk.core#CryptographicMaterialsManagerReference
use aws.encryptionSdk.core#EncryptionContext
use aws.encryptionSdk.core#AlgorithmSuiteId
use aws.encryptionSdk.core#CommitmentPolicy
use aws.polymorph#reference

/////////////
// ESDK Client Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
service AwsEncryptionSdkFactory {
    version: "2020-10-24",
    operations: [CreateDefaultAwsEncryptionSdk, CreateAwsEncryptionSdk],
    errors: [AwsEncryptionSdkException],
}

operation CreateDefaultAwsEncryptionSdk {
    output: AwsEncryptionSdkReference,
    errors: [AwsEncryptionSdkException],
}

operation CreateAwsEncryptionSdk {
    input: AwsEncryptionSdkConfig,
    output: AwsEncryptionSdkReference,
    errors: [AwsEncryptionSdkException],
}

structure AwsEncryptionSdkConfig {
    commitmentPolicy: CommitmentPolicy,
    maxEncryptedDataKeys: Long,
}

@reference(resource: AwsEncryptionSdk)
structure AwsEncryptionSdkReference {}

/////////////
// ESDK

resource AwsEncryptionSdk {
    operations: [Encrypt, Decrypt],
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

    encryptionContext: EncryptionContext,

    // One of keyring or CMM are required
    materialsManager: CryptographicMaterialsManagerReference,
    keyring: KeyringReference,

    algorithmSuiteId: AlgorithmSuiteId,

    frameLength: Long
}

structure EncryptOutput {
    @required
    ciphertext: Blob,

    @required
    encryptionContext: EncryptionContext,

    @required
    algorithmSuiteId: AlgorithmSuiteId,
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
    materialsManager: CryptographicMaterialsManagerReference,
    keyring: KeyringReference,
}

structure DecryptOutput {
    @required
    plaintext: Blob,

    @required
    encryptionContext: EncryptionContext,

    @required
    algorithmSuiteId: AlgorithmSuiteId,

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
