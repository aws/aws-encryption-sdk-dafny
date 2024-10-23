// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetActiveBranchKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub branch_key_identifier: ::std::option::Option<::std::string::String>,
}
impl GetActiveBranchKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_identifier(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_identifier
}
}
impl GetActiveBranchKeyInput {
    /// Creates a new builder-style object to manufacture [`GetActiveBranchKeyInput`](crate::deps::aws_cryptography_keyStore::types::GetActiveBranchKeyInput).
    pub fn builder() -> crate::deps::aws_cryptography_keyStore::types::builders::GetActiveBranchKeyInputBuilder {
        crate::deps::aws_cryptography_keyStore::types::builders::GetActiveBranchKeyInputBuilder::default()
    }
}

/// A builder for [`GetActiveBranchKeyInput`](crate::deps::aws_cryptography_keyStore::types::GetActiveBranchKeyInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetActiveBranchKeyInputBuilder {
    pub(crate) branch_key_identifier: ::std::option::Option<::std::string::String>,
}
impl GetActiveBranchKeyInputBuilder {
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
    /// Consumes the builder and constructs a [`GetActiveBranchKeyInput`](crate::deps::aws_cryptography_keyStore::types::GetActiveBranchKeyInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::types::GetActiveBranchKeyInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_keyStore::types::GetActiveBranchKeyInput {
            branch_key_identifier: self.branch_key_identifier,
        })
    }
}
