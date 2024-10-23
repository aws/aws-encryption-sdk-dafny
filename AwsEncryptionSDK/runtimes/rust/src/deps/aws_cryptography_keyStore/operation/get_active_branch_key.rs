// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetActiveBranchKey`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetActiveBranchKey;
impl GetActiveBranchKey {
    /// Creates a new `GetActiveBranchKey`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::deps::aws_cryptography_keyStore::client::Client,
        input: crate::deps::aws_cryptography_keyStore::operation::get_active_branch_key::GetActiveBranchKeyInput,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::operation::get_active_branch_key::GetActiveBranchKeyOutput,
        crate::deps::aws_cryptography_keyStore::types::error::Error,
    > {
        if input.branch_key_identifier.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "branch_key_identifier",
        "branch_key_identifier was not specified but it is required when building GetActiveBranchKeyInput",
    )).map_err(crate::deps::aws_cryptography_keyStore::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::deps::aws_cryptography_keyStore::conversions::get_active_branch_key::_get_active_branch_key_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetActiveBranchKey(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::deps::aws_cryptography_keyStore::conversions::get_active_branch_key::_get_active_branch_key_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::deps::aws_cryptography_keyStore::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::deps::aws_cryptography_keyStore::operation::get_active_branch_key::_get_active_branch_key_output::GetActiveBranchKeyOutput;

pub use crate::deps::aws_cryptography_keyStore::operation::get_active_branch_key::_get_active_branch_key_input::GetActiveBranchKeyInput;

pub(crate) mod _get_active_branch_key_output;

pub(crate) mod _get_active_branch_key_input;

/// Builders
pub mod builders;
