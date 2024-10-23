// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_primitives::operation::ecdsa_sign::_ecdsa_sign_output::EcdsaSignOutputBuilder;

pub use crate::deps::aws_cryptography_primitives::operation::ecdsa_sign::_ecdsa_sign_input::EcdsaSignInputBuilder;

impl EcdsaSignInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_primitives::client::Client,
    ) -> ::std::result::Result<
        ::aws_smithy_types::Blob,
        crate::deps::aws_cryptography_primitives::types::error::Error,
    > {
        let mut fluent_builder = client.ecdsa_sign();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `EcdsaSign`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct EcdsaSignFluentBuilder {
    client: crate::deps::aws_cryptography_primitives::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_primitives::operation::ecdsa_sign::builders::EcdsaSignInputBuilder,
}
impl EcdsaSignFluentBuilder {
    /// Creates a new `EcdsaSign`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_primitives::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the EcdsaSign as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_primitives::operation::ecdsa_sign::builders::EcdsaSignInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        ::aws_smithy_types::Blob,
        crate::deps::aws_cryptography_primitives::types::error::Error,
    > {
        let input = self
            .inner
            .build()
            // Using Opaque since we don't have a validation-specific error yet.
            // Operations' models don't declare their own validation error,
            // and smithy-rs seems to not generate a ValidationError case unless there is.
            // Vanilla smithy-rs uses SdkError::construction_failure, but we aren't using SdkError.
            .map_err(|mut e| crate::deps::aws_cryptography_primitives::types::error::Error::Opaque {
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any),
		alt_text : format!("{:?}", e)
            })?;
        crate::deps::aws_cryptography_primitives::operation::ecdsa_sign::EcdsaSign::send(&self.client, input).await
    }

    #[allow(missing_docs)]
pub fn message(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.message(input.into());
    self
}
#[allow(missing_docs)]
pub fn set_message(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_message(input);
    self
}
#[allow(missing_docs)]
pub fn get_message(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_message()
}
#[allow(missing_docs)]
pub fn signature_algorithm(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_primitives::types::EcdsaSignatureAlgorithm>) -> Self {
    self.inner = self.inner.signature_algorithm(input.into());
    self
}
#[allow(missing_docs)]
pub fn set_signature_algorithm(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdsaSignatureAlgorithm>) -> Self {
    self.inner = self.inner.set_signature_algorithm(input);
    self
}
#[allow(missing_docs)]
pub fn get_signature_algorithm(&self) -> &::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdsaSignatureAlgorithm> {
    self.inner.get_signature_algorithm()
}
#[allow(missing_docs)]
pub fn signing_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.signing_key(input.into());
    self
}
#[allow(missing_docs)]
pub fn set_signing_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_signing_key(input);
    self
}
#[allow(missing_docs)]
pub fn get_signing_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_signing_key()
}
}
