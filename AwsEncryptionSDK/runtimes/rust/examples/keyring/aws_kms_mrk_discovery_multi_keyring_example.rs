// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example sets up the AWS KMS MRK (multi-region key) Discovery Multi Keyring

AWS KMS MRK Discovery Multi Keyring is composed of multiple MRK discovery keyrings.

The AWS KMS discovery keyring is an AWS KMS keyring that doesn't specify any wrapping keys.

When decrypting, an MRK discovery keyring allows the AWS Encryption SDK to ask AWS KMS to decrypt
any encrypted data key by using the AWS KMS MRK that encrypted it, regardless of who owns or
has access to that AWS KMS key. The call succeeds only when the caller has kms:Decrypt
permission on the AWS KMS MRK.

The AWS Encryption SDK provides a standard AWS KMS discovery keyring and a discovery keyring
for AWS KMS multi-Region keys. Because it doesn't specify any wrapping keys, a discovery keyring
can't encrypt data. If you use a discovery keyring to encrypt data, alone or in a multi-keyring,
the encrypt operation fails.

The AWS Key Management Service (AWS KMS) MRK keyring interacts with AWS KMS to
create, encrypt, and decrypt data keys with multi-region AWS KMS keys (MRKs).
This example creates a KMS MRK Keyring and then encrypts a custom input EXAMPLE_DATA
with an encryption context. This encrypted ciphertext is then decrypted using an
MRK Discovery Multi keyring. This example also includes some sanity checks for demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
These sanity checks are for demonstration in the example only. You do not need these in your code.

For information about using multi-Region keys with the AWS Encryption SDK, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/configure.html#config-mrks

For more info on KMS MRKs (multi-region keys), see the KMS documentation:
https://docs.aws.amazon.com/kms/latest/developerguide/multi-region-keys-overview.html

For more information on how to use KMS Discovery keyrings, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/use-kms-keyring.html#kms-keyring-discovery

For more information on KMS Key identifiers, see
https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#key-id
*/

use aws_esdk::client as esdk_client;
use aws_esdk::types::aws_encryption_sdk_config::AwsEncryptionSdkConfig;
use aws_esdk::aws_cryptography_materialProviders::client as mpl_client;
use aws_esdk::aws_cryptography_materialProviders::types::material_providers_config::MaterialProvidersConfig;
use aws_esdk::aws_cryptography_materialProviders::types::DiscoveryFilter;
use std::collections::HashMap;
use aws_config::Region;

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
    mrk_key_id_encrypt: &str,
    mrk_encrypt_region: String,
    aws_account_id: &str,
    aws_regions: Vec<String>,
) -> Result<(), crate::BoxError> {
    // 1. Instantiate the encryption SDK client.
    // This builds the default client with the RequireEncryptRequireDecrypt commitment policy,
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

    // 3. Create the keyring that determines how your data keys are protected.
    // Although this example highlights Discovery keyrings, Discovery keyrings cannot
    // be used to encrypt, so for encryption we create an MRK keyring without discovery mode.
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    // Create a KMS client in the first region
    let sdk_config = aws_config::load_defaults(aws_config::BehaviorVersion::latest()).await;
    let encrypt_kms_config = aws_sdk_kms::config::Builder::from(&sdk_config)
        .region(Region::new(mrk_encrypt_region))
        .build();
    let encrypt_kms_client = aws_sdk_kms::Client::from_conf(encrypt_kms_config);

    // Create a keyring that will encrypt your data, using a KMS MRK in the first region.
    let encrypt_kms_keyring = mpl
        .create_aws_kms_mrk_keyring()
        .kms_key_id(mrk_key_id_encrypt)
        .kms_client(encrypt_kms_client)
        .send()
        .await?;

    // 4. Encrypt the data with the encryptionContext using the encrypt_keyring.
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(encrypt_kms_keyring)
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

    // 6. Now create a MRK Discovery Multi Keyring to use for decryption.
    // We'll add a discovery filter to limit the set of encrypted data keys
    // we are willing to decrypt to only ones created by KMS keys in select
    // accounts and the partition `aws`.
    // MRK Discovery keyrings also filter encrypted data keys by the region
    // the keyring is created with.
    let discovery_filter = DiscoveryFilter::builder()
        .account_ids(vec![aws_account_id.to_string()])
        .partition("aws".to_string())
        .build()?;

    // This is a Multi Keyring composed of Discovery Keyrings.
    // There is a keyring for every region in `regions`.
    // All the keyrings have the same Discovery Filter.
    // Each keyring has its own KMS Client, which is created for the keyring's region.
    let discovery_multi_keyring = mpl
        .create_aws_kms_mrk_discovery_multi_keyring()
        .regions(aws_regions)
        .discovery_filter(discovery_filter)
        .send()
        .await?;

    // 7. Decrypt your encrypted data using the discovery multi keyring.
    // On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
    // The header contains the Encrypted Data Keys (EDKs), which, if the EDK
    // was encrypted by a KMS Keyring, includes the KMS Key ARN.
    // For each member of the Multi Keyring, every EDK will try to be decrypted until a decryption
    // is successful.
    // Since every member of the Multi Keyring is a Discovery Keyring:
    //   Each Keyring will filter the EDKs by the Discovery Filter and the Keyring's region.
    //      For each filtered EDK, the keyring will attempt decryption with the keyring's client.
    // All of this is done serially, until a success occurs or all keyrings have failed
    // all (filtered) EDKs. KMS MRK Discovery Keyrings will attempt to decrypt
    // Multi Region Keys (MRKs) and regular KMS Keys.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext)
        .keyring(discovery_multi_keyring)
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

    println!("KMS MRK Discovery Multi Keyring Example Completed Successfully");

    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the AWS KMS MRK Discovery Multi Keyring example
    use crate::example_utils::utils;

    let mrk_encrypt_region: String = "us-east-1".to_string();
    let aws_regions: Vec<String> = vec!["us-east-1".to_string(), "us-west-2".to_string()];

    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_MRK_KEY_ID_US_EAST_1,
        mrk_encrypt_region,
        utils::TEST_DEFAULT_KMS_KEY_ACCOUNT_ID,
        aws_regions,
    ).await?;

    Ok(())
}