// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example sets up the Raw AES Keyring

The Raw AES keyring lets you use an AES symmetric key that you provide as a wrapping key that
protects your data key. You need to generate, store, and protect the key material,
preferably in a hardware security module (HSM) or key management system. Use a Raw AES keyring
when you need to provide the wrapping key and encrypt the data keys locally or offline.

This example creates a Raw AES Keyring and then encrypts a custom input EXAMPLE_DATA
with an encryption context. This example also includes some sanity checks for demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
These sanity checks are for demonstration in the example only. You do not need these in your code.

The Raw AES keyring encrypts data by using the AES-GCM algorithm and a wrapping key that
you specify as a byte array. You can specify only one wrapping key in each Raw AES keyring,
but you can include multiple Raw AES keyrings, alone or with other keyrings, in a multi-keyring.

For more information on how to use Raw AES keyrings, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/use-raw-aes-keyring.html
*/

use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use aws_esdk::aws_cryptography_materialProviders::types::AesWrappingAlg;
use std::collections::HashMap;
use rand::RngCore;

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
) -> Result<(), crate::BoxError> {
    // 1. Instantiate the encryption SDK client.
    // This builds the default client with the RequireEncryptRequireDecrypt commitment policy,
    // which enforces that this client only encrypts using committing algorithm suites and enforces
    // that this client will only decrypt encrypted messages that were created with a committing
    // algorithm suite.
    let esdk_config = AwsEncryptionSdkConfig::builder().build()?;
    let esdk_client = esdk_client::Client::from_conf(esdk_config)?;

    // 2. The key namespace and key name are defined by you.
    // and are used by the Raw AES keyring to determine
    // whether it should attempt to decrypt an encrypted data key.
    // For more information, see
    // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/use-raw-aes-keyring.html
    let key_namespace: &str = "my-key-namespace";
    let key_name: &str = "my-aes-key-name";

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

    // 4. Generate a 256-bit AES key to use with your keyring.
    // In practice, you should get this key from a secure key management system such as an HSM.
    let aes_key_bytes = generate_aes_key_bytes();

    // 5. Create a Raw AES Keyring
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    let raw_aes_keyring = mpl
        .create_raw_aes_keyring()
        .key_name(key_name)
        .key_namespace(key_namespace)
        .wrapping_key(aws_smithy_types::Blob::new(aes_key_bytes))
        .wrapping_alg(AesWrappingAlg::AlgAes256GcmIv12Tag16)
        .send()
        .await?;

    // 6. Encrypt the data with the encryptionContext
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(raw_aes_keyring.clone())
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let ciphertext = encryption_response
                        .ciphertext
                        .expect("Unable to unwrap ciphertext from encryption response");

    // 7. Demonstrate that the ciphertext and plaintext are different.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_ne!(ciphertext, plaintext,
        "Ciphertext and plaintext data are the same. Invalid encryption");

    // 8. Decrypt your encrypted data using the same keyring you used on encrypt.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext)
        .keyring(raw_aes_keyring)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context)
        .send()
        .await?;

    let decrypted_plaintext = decryption_response
                                .plaintext
                                .expect("Unable to unwrap plaintext from decryption response");

    // 9. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    println!("Raw AES Keyring Example Completed Successfully");

    Ok(())
}

fn generate_aes_key_bytes() -> Vec<u8> {
    // This example returns a random AES key.
    // In practice, you should not generate this key in your code, and should instead
    //     retrieve this key from a secure key management system (e.g. HSM).
    // This key is created here for example purposes only and should not be used for any other purpose.
    let mut random_bytes = [0u8; 32];
    rand::rngs::OsRng.fill_bytes(&mut random_bytes);

    random_bytes.to_vec()
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the Raw AES Keyring example
    use crate::example_utils::utils;

    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
    ).await?;

    Ok(())
}
