// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct PublicKeyDiscoveryInput {
    #[allow(missing_docs)] // documentation missing in model
pub recipient_static_private_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl PublicKeyDiscoveryInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn recipient_static_private_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.recipient_static_private_key
}
}
impl PublicKeyDiscoveryInput {
    /// Creates a new builder-style object to manufacture [`PublicKeyDiscoveryInput`](crate::deps::aws_cryptography_materialProviders::types::PublicKeyDiscoveryInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::PublicKeyDiscoveryInputBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::PublicKeyDiscoveryInputBuilder::default()
    }
}

/// A builder for [`PublicKeyDiscoveryInput`](crate::deps::aws_cryptography_materialProviders::types::PublicKeyDiscoveryInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct PublicKeyDiscoveryInputBuilder {
    pub(crate) recipient_static_private_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl PublicKeyDiscoveryInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn recipient_static_private_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.recipient_static_private_key = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_recipient_static_private_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.recipient_static_private_key = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_recipient_static_private_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.recipient_static_private_key
}
    /// Consumes the builder and constructs a [`PublicKeyDiscoveryInput`](crate::deps::aws_cryptography_materialProviders::types::PublicKeyDiscoveryInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::PublicKeyDiscoveryInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::PublicKeyDiscoveryInput {
            recipient_static_private_key: self.recipient_static_private_key,
        })
    }
}
