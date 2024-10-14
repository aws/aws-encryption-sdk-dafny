// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
 Demonstrate an encrypt/decrypt cycle using a Custom Cryptographic Materials Manager (CMM).
 `SigningSuiteOnlyCMM.cs` demonstrates creating a custom CMM to reject Non-Signing Algorithms.
*/

use super::signing_suite_only_cmm::SigningSuiteOnlyCMM;
use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::types::error::Error::AwsCryptographicMaterialProvidersError;
use aws_esdk::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use aws_esdk::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef;
use aws_esdk::aws_cryptography_materialProviders::types::EsdkAlgorithmSuiteId;
use std::collections::HashMap;

pub async fn encrypt_and_decrypt_with_cmm(
    example_data: &str,
    kms_key_id: &str,
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

    // 4. Create a custom SigningSuiteOnlyCMM
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    let kms_keyring = mpl
        .create_aws_kms_keyring()
        .kms_key_id(kms_key_id)
        .kms_client(kms_client)
        .send()
        .await?;

    let signing_suite_only_cmm = SigningSuiteOnlyCMM::new(kms_keyring);

    let signing_suite_only_cmm_ref: CryptographicMaterialsManagerRef = CryptographicMaterialsManagerRef {
        inner: ::std::rc::Rc::new(std::cell::RefCell::new(signing_suite_only_cmm)),
    };

    // 5. Encrypt the data with the encryption_context
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .materials_manager(signing_suite_only_cmm_ref.clone())
        .encryption_context(encryption_context.clone())
        .algorithm_suite_id(EsdkAlgorithmSuiteId::AlgAes256GcmHkdfSha512CommitKeyEcdsaP384)
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
        .materials_manager(signing_suite_only_cmm_ref.clone())
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let decrypted_plaintext = decryption_response
                                .plaintext
                                .expect("Unable to unwrap plaintext from decryption response");

    // 8. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    // 9. Demonstrate that a Non Signing Algorithm Suite will be rejected
    // by the CMM.
    let encryption_response_non_signing = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .materials_manager(signing_suite_only_cmm_ref)
        .encryption_context(encryption_context.clone())
        .algorithm_suite_id(EsdkAlgorithmSuiteId::AlgAes256GcmHkdfSha512CommitKey)
        .send()
        .await;

    match encryption_response_non_signing {
        Ok(_) => panic!("Encrypt using non signing algorithm suite MUST \
                            raise AwsCryptographicMaterialProvidersError"),
        Err(AwsCryptographicMaterialProvidersError { error: _e }) => (),
        _ => panic!("Unexpected error type"),
    }

    println!("SigningSuiteOnlyCMM Example Completed Successfully");

    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_cmm() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the SigningSuiteOnlyCMM example
    use crate::example_utils::utils;

    encrypt_and_decrypt_with_cmm(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_DEFAULT_KMS_KEY_ID
    ).await?;

    Ok(())
}
