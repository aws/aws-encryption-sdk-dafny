namespace aws.esdk

use aws.crypto#KeyringReference
use aws.crypto#CryptographicMaterialsManagerReference
use aws.crypto#EncryptionContext
use aws.crypto#AlgorithmSuiteId
use aws.crypto#CommitmentPolicy
use aws.polymorph#reference

/////////////
// ESDK Client Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
service AwsEncryptionSdkClientFactory {
    version: "2020-10-24",
    operations: [CreateDefaultAwsEncryptionSdkClient, CreateAwsEncryptionSdkClient],
    errors: [AwsEncryptionSdkClientException],
}

operation CreateDefaultAwsEncryptionSdkClient {
    output: AwsEncryptionSdkClientReference,
    errors: [AwsEncryptionSdkClientException],
}

operation CreateAwsEncryptionSdkClient {
    input: AwsEncryptionSdkClientConfig,
    output: AwsEncryptionSdkClientReference,
    errors: [AwsEncryptionSdkClientException],
}

structure AwsEncryptionSdkClientConfig {
    commitmentPolicy: CommitmentPolicy,
    maxEncryptedDataKeys: Long,
}

@reference(resource: AwsEncryptionSdkClient)
structure AwsEncryptionSdkClientReference {}

/////////////
// ESDK

resource AwsEncryptionSdkClient {
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
    errors: [AwsEncryptionSdkClientException],
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
structure AwsEncryptionSdkClientException {
    @required
    message: String,
}
