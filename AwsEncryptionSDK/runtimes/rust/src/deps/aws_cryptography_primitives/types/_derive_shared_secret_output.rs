// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct DeriveSharedSecretOutput {
    #[allow(missing_docs)] // documentation missing in model
pub shared_secret: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl DeriveSharedSecretOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn shared_secret(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.shared_secret
}
}
impl DeriveSharedSecretOutput {
    /// Creates a new builder-style object to manufacture [`DeriveSharedSecretOutput`](crate::deps::aws_cryptography_primitives::types::DeriveSharedSecretOutput).
    pub fn builder() -> crate::deps::aws_cryptography_primitives::types::builders::DeriveSharedSecretOutputBuilder {
        crate::deps::aws_cryptography_primitives::types::builders::DeriveSharedSecretOutputBuilder::default()
    }
}

/// A builder for [`DeriveSharedSecretOutput`](crate::deps::aws_cryptography_primitives::types::DeriveSharedSecretOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct DeriveSharedSecretOutputBuilder {
    pub(crate) shared_secret: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl DeriveSharedSecretOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn shared_secret(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.shared_secret = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_shared_secret(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.shared_secret = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_shared_secret(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.shared_secret
}
    /// Consumes the builder and constructs a [`DeriveSharedSecretOutput`](crate::deps::aws_cryptography_primitives::types::DeriveSharedSecretOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_primitives::types::DeriveSharedSecretOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_primitives::types::DeriveSharedSecretOutput {
            shared_secret: self.shared_secret,
        })
    }
}
