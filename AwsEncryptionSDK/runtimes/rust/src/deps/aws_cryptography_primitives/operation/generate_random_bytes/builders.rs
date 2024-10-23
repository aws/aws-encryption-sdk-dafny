// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_primitives::operation::generate_random_bytes::_generate_random_bytes_output::GenerateRandomBytesOutputBuilder;

pub use crate::deps::aws_cryptography_primitives::operation::generate_random_bytes::_generate_random_bytes_input::GenerateRandomBytesInputBuilder;

impl GenerateRandomBytesInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_primitives::client::Client,
    ) -> ::std::result::Result<
        ::aws_smithy_types::Blob,
        crate::deps::aws_cryptography_primitives::types::error::Error,
    > {
        let mut fluent_builder = client.generate_random_bytes();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GenerateRandomBytes`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GenerateRandomBytesFluentBuilder {
    client: crate::deps::aws_cryptography_primitives::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_primitives::operation::generate_random_bytes::builders::GenerateRandomBytesInputBuilder,
}
impl GenerateRandomBytesFluentBuilder {
    /// Creates a new `GenerateRandomBytes`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_primitives::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GenerateRandomBytes as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_primitives::operation::generate_random_bytes::builders::GenerateRandomBytesInputBuilder {
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
        crate::deps::aws_cryptography_primitives::operation::generate_random_bytes::GenerateRandomBytes::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn length(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.inner = self.inner.length(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_length(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.inner = self.inner.set_length(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_length(&self) -> &::std::option::Option<::std::primitive::i32> {
    self.inner.get_length()
}
}
