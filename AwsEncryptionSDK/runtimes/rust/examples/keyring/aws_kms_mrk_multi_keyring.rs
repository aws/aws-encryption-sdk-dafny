// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example sets up the AWS KMS MRK Multi Keyring

The AWS Key Management Service (AWS KMS) MRK keyring interacts with AWS KMS to
create, encrypt, and decrypt data keys with AWS KMS MRK keys.
The KMS MRK multi-keyring consists of one or more individual keyrings of the
same or different type. The keys can either be regular KMS keys or MRKs.
The effect is like using several keyrings in a series.

This example creates a AwsKmsMrkMultiKeyring using an mrk_key_id (generator) and a kms_key_id
as a child key, and then encrypts a custom input EXAMPLE_DATA with an encryption context.
Either KMS Key individually is capable of decrypting data encrypted under this keyring.
This example also includes some sanity checks for demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
3. Ciphertext can be decrypted using an AwsKmsMrkKeyring containing a replica of the
   MRK (from the multi-keyring used for encryption) copied from the first region into
   the second region
These sanity checks are for demonstration in the example only. You do not need these in your code.

For more information on how to use KMS keyrings, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/use-kms-keyring.html

For more info on KMS MRK (multi-region keys), see the KMS documentation:
https://docs.aws.amazon.com/kms/latest/developerguide/multi-region-keys-overview.html

For more information on KMS Key identifiers, see
https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#key-id
*/

use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use std::collections::HashMap;
use aws_config::Region;

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
    mrk_key_id: &str,
    kms_key_id: &str,
    mrk_replica_key_id: &str,
    mrk_replica_decrypt_region: String,
) -> Result<(), crate::BoxError> {
    // 1. Instantiate the encryption SDK client.
    // This builds the default client with the REQUIRE_ENCRYPT_REQUIRE_DECRYPT commitment policy,
    // which enforces that this client only encrypts using committing algorithm suites and enforces
    // that this client will only decrypt encrypted messages that were created with a committing
    // algorithm suite.
    let esdk_config = AwsEncryptionSdkConfig::builder().build()?;
    let esdk_client = esdk_client::Client::from_conf(esdk_config)?;

    // 2. Create encryption context.
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

    // 3. Create an AwsKmsMrkMultiKeyring that protects your data under two different KMS Keys.
    // The Keys can either be regular KMS keys or MRKs.
    // Either KMS Key individually is capable of decrypting data encrypted under this keyring.
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    let kms_mrk_multi_keyring = mpl
        .create_aws_kms_mrk_multi_keyring()
        .generator(mrk_key_id)
        .kms_key_ids(vec![kms_key_id.to_string()])
        .send()
        .await?;

    // 4. Encrypt the data with the encryptionContext using the kms_mrk_multi_keyring.
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(kms_mrk_multi_keyring.clone())
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let ciphertext = encryption_response
                        .ciphertext
                        .expect("Unable to unwrap ciphertext from encryption response");

    // 5. Demonstrate that the ciphertext and plaintext are different.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_ne!(ciphertext, plaintext,
        "Ciphertext and plaintext data are the same. Invalid encryption");

    // 6. Decrypt your encrypted data using the same AwsKmsMrkMultiKeyring you used on encrypt.
    // It will decrypt the data using the generator key (in this case, the MRK), since that is
    // the first available KMS key on the keyring that is capable of decrypting the data.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext.clone())
        .keyring(kms_mrk_multi_keyring)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let decrypted_plaintext = decryption_response
                                .plaintext
                                .expect("Unable to unwrap plaintext from decryption response");

    // 7. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    // Demonstrate that a single AwsKmsMrkKeyring configured with a replica of the MRK from the
    // multi-keyring used to encrypt the data is also capable of decrypting the data.
    // (This is an example for demonstration; you do not need to do this in your own code.)

    // 8. Create a single AwsKmsMrkKeyring with the replica KMS MRK from the second region.

    // Create a client for KMS in the second region which is the region for mrk_replica_key_id.
    let sdk_config = aws_config::load_defaults(aws_config::BehaviorVersion::latest()).await;
    let second_region_kms_config = aws_sdk_kms::config::Builder::from(&sdk_config)
        .region(Region::new(mrk_replica_decrypt_region))
        .build();
    let second_region_kms_client = aws_sdk_kms::Client::from_conf(second_region_kms_config);

    let second_region_mrk_keyring = mpl
        .create_aws_kms_mrk_keyring()
        .kms_key_id(mrk_replica_key_id)
        .kms_client(second_region_kms_client)
        .send()
        .await?;

    // 9. Decrypt your encrypted data using the second region AwsKmsMrkKeyring
    let second_region_decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext)
        .keyring(second_region_mrk_keyring)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context)
        .send()
        .await?;

    let second_region_decrypted_plaintext = second_region_decryption_response
        .plaintext
        .expect("Unable to unwrap plaintext from decryption response");

    // 10. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(second_region_decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    // Not shown in this example: A KMS Keyring created with `kms_key_id` could also
    // decrypt this message.

    println!("KMS MRK Multi Keyring Example Completed Successfully");

    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the AWS KMS MRK Multi Keyring example
    use crate::example_utils::utils;

    let mrk_replica_decrypt_region: String = "eu-west-1".to_string();

    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_MRK_KEY_ID_US_EAST_1,
        utils::TEST_DEFAULT_KMS_KEY_ID,
        utils::TEST_MRK_KEY_ID_EU_WEST_1,
        mrk_replica_decrypt_region,
    ).await?;

    Ok(())
}
