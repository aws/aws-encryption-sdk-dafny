// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `ValidEncryptionMaterialsTransition`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct ValidEncryptionMaterialsTransition;
impl ValidEncryptionMaterialsTransition {
    /// Creates a new `ValidEncryptionMaterialsTransition`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
        input: crate::deps::aws_cryptography_materialProviders::operation::valid_encryption_materials_transition::ValidEncryptionMaterialsTransitionInput,
    ) -> ::std::result::Result<
        (),
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        if input.start.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "start",
        "start was not specified but it is required when building ValidEncryptionMaterialsTransitionInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
if input.stop.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "stop",
        "stop was not specified but it is required when building ValidEncryptionMaterialsTransitionInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::deps::aws_cryptography_materialProviders::conversions::valid_encryption_materials_transition::_valid_encryption_materials_transition_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).ValidEncryptionMaterialsTransition(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                (),
            )
        } else {
            Err(crate::deps::aws_cryptography_materialProviders::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::deps::aws_cryptography_materialProviders::operation::valid_encryption_materials_transition::_unit::Unit;

pub use crate::deps::aws_cryptography_materialProviders::operation::valid_encryption_materials_transition::_valid_encryption_materials_transition_input::ValidEncryptionMaterialsTransitionInput;

pub(crate) mod _unit;

pub(crate) mod _valid_encryption_materials_transition_input;

/// Builders
pub mod builders;
