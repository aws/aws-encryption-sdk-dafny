// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `CreateAwsKmsMrkKeyring`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct CreateAwsKmsMrkKeyring;
impl CreateAwsKmsMrkKeyring {
    /// Creates a new `CreateAwsKmsMrkKeyring`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
        input: crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_keyring::CreateAwsKmsMrkKeyringInput,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        if input.kms_key_id.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "kms_key_id",
        "kms_key_id was not specified but it is required when building CreateAwsKmsMrkKeyringInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
if input.kms_client.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "kms_client",
        "kms_client was not specified but it is required when building CreateAwsKmsMrkKeyringInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::deps::aws_cryptography_materialProviders::conversions::create_aws_kms_mrk_keyring::_create_aws_kms_mrk_keyring_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).CreateAwsKmsMrkKeyring(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::deps::aws_cryptography_materialProviders::conversions::keyring::from_dafny(inner_result.value().clone())
,
            )
        } else {
            Err(crate::deps::aws_cryptography_materialProviders::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_keyring::_create_keyring_output::CreateKeyringOutput;

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_keyring::_create_aws_kms_mrk_keyring_input::CreateAwsKmsMrkKeyringInput;

pub(crate) mod _create_keyring_output;

pub(crate) mod _create_aws_kms_mrk_keyring_input;

/// Builders
pub mod builders;
