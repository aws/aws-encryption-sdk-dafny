// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateRawRsaKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub key_name: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub key_namespace: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub padding_scheme: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme>,
#[allow(missing_docs)] // documentation missing in model
pub private_key: ::std::option::Option<::aws_smithy_types::Blob>,
#[allow(missing_docs)] // documentation missing in model
pub public_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl CreateRawRsaKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn key_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_name
}
#[allow(missing_docs)] // documentation missing in model
pub fn key_namespace(&self) -> &::std::option::Option<::std::string::String> {
    &self.key_namespace
}
#[allow(missing_docs)] // documentation missing in model
pub fn padding_scheme(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme> {
    &self.padding_scheme
}
#[allow(missing_docs)] // documentation missing in model
pub fn private_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.private_key
}
#[allow(missing_docs)] // documentation missing in model
pub fn public_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.public_key
}
}
impl CreateRawRsaKeyringInput {
    /// Creates a new builder-style object to manufacture [`CreateRawRsaKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawRsaKeyringInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::CreateRawRsaKeyringInputBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::CreateRawRsaKeyringInputBuilder::default()
    }
}

/// A builder for [`CreateRawRsaKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawRsaKeyringInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateRawRsaKeyringInputBuilder {
    pub(crate) key_name: ::std::option::Option<::std::string::String>,
pub(crate) key_namespace: ::std::option::Option<::std::string::String>,
pub(crate) padding_scheme: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme>,
pub(crate) private_key: ::std::option::Option<::aws_smithy_types::Blob>,
pub(crate) public_key: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl CreateRawRsaKeyringInputBuilder {
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
pub fn padding_scheme(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme>) -> Self {
    self.padding_scheme = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_padding_scheme(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme>) -> Self {
    self.padding_scheme = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_padding_scheme(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::PaddingScheme> {
    &self.padding_scheme
}
#[allow(missing_docs)] // documentation missing in model
pub fn private_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.private_key = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_private_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.private_key = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_private_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.private_key
}
#[allow(missing_docs)] // documentation missing in model
pub fn public_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.public_key = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_public_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.public_key = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_public_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.public_key
}
    /// Consumes the builder and constructs a [`CreateRawRsaKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateRawRsaKeyringInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::CreateRawRsaKeyringInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::CreateRawRsaKeyringInput {
            key_name: self.key_name,
key_namespace: self.key_namespace,
padding_scheme: self.padding_scheme,
private_key: self.private_key,
public_key: self.public_key,
        })
    }
}
