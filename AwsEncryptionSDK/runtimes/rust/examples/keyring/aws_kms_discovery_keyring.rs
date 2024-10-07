// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
This example sets up the AWS KMS Discovery Keyring

AWS KMS discovery keyring is an AWS KMS keyring that doesn't specify any wrapping keys.

The AWS Encryption SDK provides a standard AWS KMS discovery keyring and a discovery keyring
for AWS KMS multi-Region keys. For information about using multi-Region keys with the
AWS Encryption SDK, see
https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/configure.html#config-mrks

Because it doesn't specify any wrapping keys, a discovery keyring can't encrypt data.
If you use a discovery keyring to encrypt data, alone or in a multi-keyring, the encrypt
operation fails.

When decrypting, a discovery keyring allows the AWS Encryption SDK to ask AWS KMS to decrypt
any encrypted data key by using the AWS KMS key that encrypted it, regardless of who owns or
has access to that AWS KMS key. The call succeeds only when the caller has kms:Decrypt
permission on the AWS KMS key.

This example creates a KMS Keyring and then encrypts a custom input EXAMPLE_DATA
with an encryption context. This encrypted ciphertext is then decrypted using the Discovery keyring.
This example also includes some sanity checks for demonstration:
1. Ciphertext and plaintext data are not the same
2. Decrypted plaintext value matches EXAMPLE_DATA
3. Decryption is only possible if the Discovery Keyring contains the correct AWS Account ID's to
    which the KMS key used for encryption belongs
These sanity checks are for demonstration in the example only. You do not need these in your code.

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

pub async fn encrypt_and_decrypt_with_keyring(
    example_data: &str,
    kms_key_id: &str,
    aws_account_id: &str,
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

    // 4. Create the keyring that determines how your data keys are protected.
    //    Although this example highlights Discovery keyrings, Discovery keyrings cannot
    //    be used to encrypt, so for encryption we create a KMS keyring without discovery mode.
    let mpl_config = MaterialProvidersConfig::builder().build()?;
    let mpl = mpl_client::Client::from_conf(mpl_config)?;

    let kms_keyring = mpl
        .create_aws_kms_keyring()
        .kms_key_id(kms_key_id)
        .kms_client(kms_client.clone())
        .send()
        .await?;

    // 5. Encrypt the data with the encryption_context
    let plaintext = aws_smithy_types::Blob::new(example_data);

    let encryption_response = esdk_client.encrypt()
        .plaintext(plaintext.clone())
        .keyring(kms_keyring.clone())
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let ciphertext = encryption_response
                        .ciphertext
                        .expect("Unable to unwrap ciphertext from encryption_response");

    // 6. Demonstrate that the ciphertext and plaintext are different.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_ne!(ciphertext, plaintext,
        "Ciphertext and plaintext data are the same. Invalid encryption");

    // 7. Now create a Discovery keyring to use for decryption. We'll add a discovery filter
    //    so that we limit the set of ciphertexts we are willing to decrypt to only ones
    //    created by KMS keys in our account and partition.
    let discovery_filter = DiscoveryFilter::builder()
        .account_ids(vec![aws_account_id.to_string()])
        .partition("aws".to_string())
        .build()?;

    let discovery_keyring = mpl
        .create_aws_kms_discovery_keyring()
        .kms_client(kms_client.clone())
        .discovery_filter(discovery_filter)
        .send()
        .await?;

    // 8. Decrypt your encrypted data using the discovery keyring.
    //    On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
    //    The header contains the Encrypted Data Keys (EDKs), which, if the EDK
    //    was encrypted by a KMS Keyring, includes the KMS Key ARN.
    //    The Discovery Keyring filters these EDKs for
    //    EDKs encrypted by Single Region OR Multi Region KMS Keys.
    //    If a Discovery Filter is present, these KMS Keys must belong
    //    to an AWS Account ID in the discovery filter's AccountIds and
    //    must be from the discovery filter's partition.
    //    Finally, KMS is called to decrypt each filtered EDK until an EDK is
    //    successfully decrypted. The resulting data key is used to decrypt the
    //    ciphertext's message.
    //    If all calls to KMS fail, the decryption fails.
    let decryption_response = esdk_client.decrypt()
        .ciphertext(ciphertext.clone())
        .keyring(discovery_keyring)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context.clone())
        .send()
        .await?;

    let decrypted_plaintext = decryption_response
                                .plaintext
                                .expect("Unable to unwrap plaintext from decryption_response");

    // 9. Demonstrate that the decrypted plaintext is identical to the original plaintext.
    // (This is an example for demonstration; you do not need to do this in your own code.)
    assert_eq!(decrypted_plaintext, plaintext,
        "Decrypted plaintext should be identical to the original plaintext. Invalid decryption");

    // 10. Demonstrate that if a different discovery keyring (Bob's) doesn't have the correct
    //     AWS Account ID's, the decrypt will fail with an error message
    //     Note that this assumes Account ID used here ('888888888888') is different than the one used
    //     during encryption
    let discovery_filter_bob = DiscoveryFilter::builder()
        .account_ids(vec!["888888888888".to_string()])
        .partition("aws".to_string())
        .build()?;

    let discovery_keyring_bob = mpl
        .create_aws_kms_discovery_keyring()
        .kms_client(kms_client)
        .discovery_filter(discovery_filter_bob)
        .send()
        .await?;

    // Decrypt the ciphertext using Bob's discovery keyring which doesn't contain the required
    // Account ID's for the KMS keyring used for encryption.
    // This should throw an AwsCryptographicMaterialProvidersError exception
    let decryption_response_bob = esdk_client.decrypt()
        .ciphertext(ciphertext)
        .keyring(discovery_keyring_bob)
        // Provide the encryption context that was supplied to the encrypt method
        .encryption_context(encryption_context)
        .send()
        .await;

    match decryption_response_bob {
        Ok(_) => {
            panic!("Decrypt using discovery keyring with wrong AWS Account ID should \
                    raise AWSEncryptionSDKClientError");
        }
        Err(e) => {
            assert_eq!(e.to_string()[.."AwsCryptographicMaterialProvidersError".to_string().chars().count()], "AwsCryptographicMaterialProvidersError".to_string());
        }
    }
    
    println!("KMS Discovery Keyring Example Completed Successfully");
    
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_encrypt_and_decrypt_with_keyring() -> Result<(), crate::BoxError2> {
    // Test function for encrypt and decrypt using the AWS KMS Discovery Keyring example
    use crate::example_utils::utils;
    
    encrypt_and_decrypt_with_keyring(
        utils::TEST_EXAMPLE_DATA,
        utils::TEST_DEFAULT_KMS_KEY_ID,
        utils::TEST_DEFAULT_KMS_KEY_ACCOUNT_ID
    ).await?;

    Ok(())
}
