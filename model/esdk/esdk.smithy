namespace aws.esdk

use aws.crypto#KeyringReference
use aws.crypto#CryptographicMaterialsManagerReference
use aws.crypto#EncryptionContext
use aws.crypto#AlgorithmSuiteId
use aws.crypto#CommitmentPolicy
use aws.polymorph#reference
use aws.polymorph#clientConfig

@clientConfig(config: AwsEncryptionSdkClientConfig)
service AwsEncryptionSdk {
    version: "2020-10-24",
    operations: [Encrypt, Decrypt],
    errors: [AwsEncryptionSdkClientException],
}

structure AwsEncryptionSdkClientConfig {
    commitmentPolicy: CommitmentPolicy,
    maxEncryptedDataKeys: Long,

    @required
    configDefaults: ConfigurationDefaults
}

@error("client")
structure AwsEncryptionSdkClientException {
    @required
    message: String,
}

///////////////////
// Default Versions

@enum([
    {
        name: "V1",
        value: "V1",
    }
])
string ConfigurationDefaults

/////////////
// Operations

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
