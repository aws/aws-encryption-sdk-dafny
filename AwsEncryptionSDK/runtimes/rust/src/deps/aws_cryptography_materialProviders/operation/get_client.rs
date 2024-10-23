// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetClient`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetClient;
impl GetClient {
    /// Creates a new `GetClient`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client_supplier: &crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef,
        input: crate::deps::aws_cryptography_materialProviders::operation::get_client::GetClientInput,
    ) -> ::std::result::Result<
        crate::deps::com_amazonaws_kms::client::Client,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        if input.region.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "region",
        "region was not specified but it is required when building GetClientInput",
    )).map_err(crate::deps::aws_cryptography_materialProviders::types::error::Error::wrap_validation_err);
}
        client_supplier.inner.borrow_mut().get_client(input)
    }
}

pub use crate::deps::aws_cryptography_materialProviders::operation::get_client::_get_client_output::GetClientOutput;

pub use crate::deps::aws_cryptography_materialProviders::operation::get_client::_get_client_input::GetClientInput;

pub(crate) mod _get_client_output;

pub(crate) mod _get_client_input;

/// Builders
pub mod builders;
