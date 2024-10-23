// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateRawAesKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub key_name: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub key_namespace: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub wrapping_alg: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg>,
#[allow(missing_docs)] // documentation missing in model
pub wrapping_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl CreateRawAesKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn key_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_name
}
#[allow(missing_docs)] // documentation missing in model
pub fn key_namespace(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_namespace
}
#[allow(missing_docs)] // documentation missing in model
pub fn wrapping_alg(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg> {
    &self.wrapping_alg
}
#[allow(missing_docs)] // documentation missing in model
pub fn wrapping_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.wrapping_key
}
}
impl CreateRawAesKeyringInput {
    /// Creates a new builder-style object to manufacture [`CreateRawAesKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawAesKeyringInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::CreateRawAesKeyringInputBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::CreateRawAesKeyringInputBuilder::default()
    }
}

/// A builder for [`CreateRawAesKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawAesKeyringInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateRawAesKeyringInputBuilder {
    pub(crate) key_name: ::std::option::Option<::std::string::String>,
pub(crate) key_namespace: ::std::option::Option<::std::string::String>,
pub(crate) wrapping_alg: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg>,
pub(crate) wrapping_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl CreateRawAesKeyringInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn key_name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.key_name = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_key_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.key_name = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_key_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_name
}
#[allow(missing_docs)] // documentation missing in model
pub fn key_namespace(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.key_namespace = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_key_namespace(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.key_namespace = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_key_namespace(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_namespace
}
#[allow(missing_docs)] // documentation missing in model
pub fn wrapping_alg(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg>) -> Self {
    self.wrapping_alg = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_wrapping_alg(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg>) -> Self {
    self.wrapping_alg = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_wrapping_alg(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::AesWrappingAlg> {
    &self.wrapping_alg
}
#[allow(missing_docs)] // documentation missing in model
pub fn wrapping_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.wrapping_key = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_wrapping_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.wrapping_key = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_wrapping_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.wrapping_key
}
    /// Consumes the builder and constructs a [`CreateRawAesKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawAesKeyringInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::CreateRawAesKeyringInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::CreateRawAesKeyringInput {
            key_name: self.key_name,
key_namespace: self.key_namespace,
wrapping_alg: self.wrapping_alg,
wrapping_key: self.wrapping_key,
        })
    }
}
