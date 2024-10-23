// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateMultiKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub child_keyrings: ::std::option::Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>>,
#[allow(missing_docs)] // documentation missing in model
pub generator: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>,
}
impl CreateMultiKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn child_keyrings(&self) -> &::std::option::Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>> {
    &self.child_keyrings
}
#[allow(missing_docs)] // documentation missing in model
pub fn generator(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef> {
    &self.generator
}
}
impl CreateMultiKeyringInput {
    /// Creates a new builder-style object to manufacture [`CreateMultiKeyringInput`](crate::operation::create_multi_keyring::builders::CreateMultiKeyringInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::operation::create_multi_keyring::builders::CreateMultiKeyringInputBuilder {
        crate::deps::aws_cryptography_materialProviders::operation::create_multi_keyring::builders::CreateMultiKeyringInputBuilder::default()
    }
}

/// A builder for [`CreateMultiKeyringInput`](crate::operation::operation::CreateMultiKeyringInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateMultiKeyringInputBuilder {
    pub(crate) child_keyrings: ::std::option::Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>>,
pub(crate) generator: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>,
}
impl CreateMultiKeyringInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn child_keyrings(mut self, input: impl ::std::convert::Into<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>>) -> Self {
    self.child_keyrings = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_child_keyrings(mut self, input: ::std::option::Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>>) -> Self {
    self.child_keyrings = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_child_keyrings(&self) -> &::std::option::Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>> {
    &self.child_keyrings
}
#[allow(missing_docs)] // documentation missing in model
pub fn generator(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>) -> Self {
    self.generator = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_generator(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>) -> Self {
    self.generator = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_generator(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef> {
    &self.generator
}
    /// Consumes the builder and constructs a [`CreateMultiKeyringInput`](crate::operation::operation::CreateMultiKeyringInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::operation::create_multi_keyring::CreateMultiKeyringInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::operation::create_multi_keyring::CreateMultiKeyringInput {
            child_keyrings: self.child_keyrings,
generator: self.generator,
        })
    }
}
