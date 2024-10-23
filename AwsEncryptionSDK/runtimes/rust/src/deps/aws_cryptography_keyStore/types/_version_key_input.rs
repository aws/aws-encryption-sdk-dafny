// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct VersionKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub branch_key_identifier: ::std::option::Option<::std::string::String>,
}
impl VersionKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_identifier(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_identifier
}
}
impl VersionKeyInput {
    /// Creates a new builder-style object to manufacture [`VersionKeyInput`](crate::deps::aws_cryptography_keyStore::types::VersionKeyInput).
    pub fn builder() -> crate::deps::aws_cryptography_keyStore::types::builders::VersionKeyInputBuilder {
        crate::deps::aws_cryptography_keyStore::types::builders::VersionKeyInputBuilder::default()
    }
}

/// A builder for [`VersionKeyInput`](crate::deps::aws_cryptography_keyStore::types::VersionKeyInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct VersionKeyInputBuilder {
    pub(crate) branch_key_identifier: ::std::option::Option<::std::string::String>,
}
impl VersionKeyInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_identifier(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.branch_key_identifier = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_branch_key_identifier(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.branch_key_identifier = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_branch_key_identifier(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_identifier
}
    /// Consumes the builder and constructs a [`VersionKeyInput`](crate::deps::aws_cryptography_keyStore::types::VersionKeyInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::types::VersionKeyInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_keyStore::types::VersionKeyInput {
            branch_key_identifier: self.branch_key_identifier,
        })
    }
}
