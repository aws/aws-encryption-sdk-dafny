// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example configures a client with a specific commitment policy for the
AWS Encryption SDK client, then encrypts and decrypts data using an AWS KMS Keyring.

The commitment policy in this example (ForbidEncryptAllowDecrypt) should only be
used as part of a migration from version 1.x to 2.x, or for advanced users with
specialized requirements. Most AWS Encryption SDK users should use the default
commitment policy (RequireEncryptRequireDecrypt).

This example creates a KMS Keyring and then encrypts a custom input EXAMPLE_DATA
with an encryption context for the commitment policy ForbidEncryptAllowDecrypt.
This example also includes some sanity checks for demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
These sanity checks are for demonstration in the example only. You do not need these in your code.

For more information on setting your commitment policy, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#commitment-policy

For more information on KMS Key identifiers, see
https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#key-id
*/

use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::aws_cryptography_materialProviders::types::EsdkCommitmentPolicy::ForbidEncryptAllowDecrypt;
use aws_esdk::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use std::collections::HashMap;

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
    kms_key_id: &str,
) -> Result<(), crate::BoxError> {
    // 1. Instantiate the encryption SDK client.
    // This example builds the client with the ForbidEncryptAllowDecrypt commitment policy,
    // which enforces that this client cannot encrypt with key commitment
    // and it can decrypt ciphertexts encrypted with or without key commitment.
    // The default commitment policy if you were to build the client like in
    // the `keyring/aws_kms_keyring_example.rs` is RequireEncryptRequireDecrypt.
    // We recommend that AWS Encryption SDK users use the default commitment policy
    // (RequireEncryptRequireDecrypt) whenever possible.
    let esdk_config = AwsEncryptionSdkConfig::builder()
                        .commitment_policy(ForbidEncryptAllowDecrypt)
                        .build()?;
    let esdk_client = esdk_client::Client::from_conf(esdk_config)?;

    // 2. Create a KMS client.
    let sdk_config = aws_config::load_defaults(aws_config::BehaviorVersion::latest()).await;
    let kms_client = aws_sdk_kms::Client::new(&sdk_config);

    // 3. Create encryption context.
    // Remember that your encryption context is NOT SECRET.
    // For more information, see
    // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
    let encryption_context = HashMap::from([
        ("encryption".to_string(), "context".to_string()),
        ("is not".to_string(), "secret".to_string()),
        ("but adds".to_string(), "useful metadata".to_string()),
        ("that can help you".to_string(), "be confident that".to_string()),
        ("the data you are handling".to_string(), "is what you think it is".to_string()),
    ]);

    // 4. Create a KMS keyring
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    let kms_keyring = mpl
        .create_aws_kms_keyring()
        .kms_key_id(kms_key_id)
        .kms_client(kms_client)
        .send()
        .await?;

    // 5. Encrypt the data with the encryptionContext. Make sure you use a non-committing algorithm
    // with the commitment policy ForbidEncryptAllowDecrypt. Otherwise esdk_client.encrypt() will throw
    // Error: AwsCryptographicMaterialProvidersError
    //   {
    //     error: InvalidAlgorithmSuiteInfoOnEncrypt
    //     {
    //       message: "Configuration conflict. Commitment policy requires only non-committing algorithm suites"
    //     }
    //   }
    // By default for ForbidEncryptAllowDecrypt, the algorithm used is
    // AlgAes256GcmIv12Tag16HkdfSha384EcdsaP384 which is a non-committing algorithm.
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(kms_keyring.clone())
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let ciphertext = encryption_response
                        .ciphertext
                        .expect("Unable to unwrap ciphertext from encryption response");

    // 6. Demonstrate that the ciphertext and plaintext are different.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_ne!(ciphertext, plaintext,
        "Ciphertext and plaintext data are the same. Invalid encryption");

    // 7. Decrypt your encrypted data using the same keyring you used on encrypt.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext)
        .keyring(kms_keyring)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context)
        .send()
        .await?;

    let decrypted_plaintext = decryption_response
                                .plaintext
                                .expect("Unable to unwrap plaintext from decryption response");

    // 8. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    println!("Set Commitment Policy Example Completed Successfully");

    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the Set Commitment Policy example
    use crate::example_utils::utils;

    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_DEFAULT_KMS_KEY_ID
    ).await?;

    Ok(())
}
