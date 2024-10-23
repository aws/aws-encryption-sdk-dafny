// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateAwsKmsMrkMultiKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub client_supplier: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>,
#[allow(missing_docs)] // documentation missing in model
pub generator: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub kms_key_ids: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
}
impl CreateAwsKmsMrkMultiKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn client_supplier(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef> {
    &self.client_supplier
}
#[allow(missing_docs)] // documentation missing in model
pub fn generator(&self) -> &::std::option::Option<::std::string::String> {
    &self.generator
}
#[allow(missing_docs)] // documentation missing in model
pub fn grant_tokens(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.grant_tokens
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_key_ids(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.kms_key_ids
}
}
impl CreateAwsKmsMrkMultiKeyringInput {
    /// Creates a new builder-style object to manufacture [`CreateAwsKmsMrkMultiKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsMrkMultiKeyringInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::CreateAwsKmsMrkMultiKeyringInputBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::CreateAwsKmsMrkMultiKeyringInputBuilder::default()
    }
}

/// A builder for [`CreateAwsKmsMrkMultiKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsMrkMultiKeyringInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateAwsKmsMrkMultiKeyringInputBuilder {
    pub(crate) client_supplier: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>,
pub(crate) generator: ::std::option::Option<::std::string::String>,
pub(crate) grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) kms_key_ids: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
}
impl CreateAwsKmsMrkMultiKeyringInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn client_supplier(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>) -> Self {
    self.client_supplier = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_client_supplier(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>) -> Self {
    self.client_supplier = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_client_supplier(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef> {
    &self.client_supplier
}
#[allow(missing_docs)] // documentation missing in model
pub fn generator(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.generator = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_generator(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.generator = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_generator(&self) -> &::std::option::Option<::std::string::String> {
    &self.generator
}
#[allow(missing_docs)] // documentation missing in model
pub fn grant_tokens(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.grant_tokens = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_grant_tokens(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.grant_tokens = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_grant_tokens(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.grant_tokens
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_key_ids(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.kms_key_ids = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_kms_key_ids(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.kms_key_ids = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_kms_key_ids(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.kms_key_ids
}
    /// Consumes the builder and constructs a [`CreateAwsKmsMrkMultiKeyringInput`](crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsMrkMultiKeyringInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsMrkMultiKeyringInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsMrkMultiKeyringInput {
            client_supplier: self.client_supplier,
generator: self.generator,
grant_tokens: self.grant_tokens,
kms_key_ids: self.kms_key_ids,
        })
    }
}
