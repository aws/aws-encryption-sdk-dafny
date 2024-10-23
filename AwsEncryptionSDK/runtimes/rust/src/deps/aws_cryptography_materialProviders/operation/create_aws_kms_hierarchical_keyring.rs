// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `CreateAwsKmsHierarchicalKeyring`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct CreateAwsKmsHierarchicalKeyring;
impl CreateAwsKmsHierarchicalKeyring {
    /// Creates a new `CreateAwsKmsHierarchicalKeyring`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
        input: crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::CreateAwsKmsHierarchicalKeyringInput,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        if input.key_store.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "key_store",
        "key_store was not specified but it is required when building CreateAwsKmsHierarchicalKeyringInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
if input.ttl_seconds.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "ttl_seconds",
        "ttl_seconds was not specified but it is required when building CreateAwsKmsHierarchicalKeyringInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
if matches!(input.ttl_seconds, Some(x) if !(0..).contains(&x)) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "ttl_seconds",
        "ttl_seconds failed to satisfy constraint: Member must be greater than or equal to 0",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::deps::aws_cryptography_materialProviders::conversions::create_aws_kms_hierarchical_keyring::_create_aws_kms_hierarchical_keyring_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).CreateAwsKmsHierarchicalKeyring(&inner_input);
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

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::_create_keyring_output::CreateKeyringOutput;

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::_create_aws_kms_hierarchical_keyring_input::CreateAwsKmsHierarchicalKeyringInput;

pub(crate) mod _create_keyring_output;

pub(crate) mod _create_aws_kms_hierarchical_keyring_input;

/// Builders
pub mod builders;
