// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example sets up the AWS KMS RSA Keyring

This example creates a KMS RSA Keyring and then encrypts a custom input
example_data with an encryption context. This example also includes some sanity checks for
demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
These sanity checks are for demonstration in the example only. You do not need these in your code.

# For more information on how to use KMS keyrings, see
# https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/use-kms-keyring.html

For more information on KMS Key identifiers, see
https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#key-id
*/

use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::deps::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::deps::aws_cryptography_materialProviders::types::EsdkAlgorithmSuiteId;
use aws_esdk::deps::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use std::collections::HashMap;

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
    kms_rsa_key_id: &str,
    kms_rsa_public_key: &str,
) -> Result<(), crate::BoxError> {
    // 1. Instantiate the encryption SDK client.
    // This builds the default client with the REQUIRE_ENCRYPT_REQUIRE_DECRYPT commitment policy,
    // which enforces that this client only encrypts using committing algorithm suites and enforces
    // that this client will only decrypt encrypted messages that were created with a committing
    // algorithm suite.
    let esdk_config = AwsEncryptionSdkConfig::builder().build()?;
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

    // 4. Create a KMS RSA keyring
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    // For more information on the allowed encryption algorithms, please see
    // https://docs.aws.amazon.com/kms/latest/developerguide/asymmetric-key-specs.html#key-spec-rsa
    let kms_rsa_keyring = mpl
        .create_aws_kms_rsa_keyring()
        .kms_key_id(kms_rsa_key_id)
        .public_key(aws_smithy_types::Blob::new(kms_rsa_public_key))
        .encryption_algorithm(aws_sdk_kms::types::EncryptionAlgorithmSpec::RsaesOaepSha256)
        .kms_client(kms_client)
        .send()
        .await?;

    // 5. Encrypt the data with the encryption_context
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(kms_rsa_keyring.clone())
        .encryption_context(encryption_context.clone())
        .algorithm_suite_id(EsdkAlgorithmSuiteId::AlgAes256GcmHkdfSha512CommitKey)
        .send()
        .await?;

    let ciphertext = encryption_response.ciphertext.unwrap();

    // 6. Demonstrate that the ciphertext and plaintext are different.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_ne!(ciphertext, plaintext,
        "Ciphertext and plaintext data are the same. Invalid encryption");
    
    // 7. Decrypt your encrypted data using the same keyring you used on encrypt.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext.clone())
        .keyring(kms_rsa_keyring.clone())
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let decrypted_plaintext = decryption_response.plaintext.unwrap();

    // 8. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");
    
    println!("KMS RSA Keyring Example Completed Successfully");
    
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    use crate::example_utils::utils;
    
    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_KMS_RSA_KEY_ID,
        utils::TEST_KMS_RSA_PUBLIC_KEY
    ).await?;

    Ok(())
}
