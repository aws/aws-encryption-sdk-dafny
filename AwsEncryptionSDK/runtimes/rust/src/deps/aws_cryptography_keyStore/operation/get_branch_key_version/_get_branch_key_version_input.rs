// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBranchKeyVersionInput {
    #[allow(missing_docs)] // documentation missing in model
pub branch_key_identifier: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub branch_key_version: ::std::option::Option<::std::string::String>,
}
impl GetBranchKeyVersionInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_identifier(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_identifier
}
#[allow(missing_docs)] // documentation missing in model
pub fn branch_key_version(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_version
}
}
impl GetBranchKeyVersionInput {
    /// Creates a new builder-style object to manufacture [`GetBranchKeyVersionInput`](crate::operation::get_branch_key_version::builders::GetBranchKeyVersionInput).
    pub fn builder() -> crate::deps::aws_cryptography_keyStore::operation::get_branch_key_version::builders::GetBranchKeyVersionInputBuilder {
        crate::deps::aws_cryptography_keyStore::operation::get_branch_key_version::builders::GetBranchKeyVersionInputBuilder::default()
    }
}

/// A builder for [`GetBranchKeyVersionInput`](crate::operation::operation::GetBranchKeyVersionInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBranchKeyVersionInputBuilder {
    pub(crate) branch_key_identifier: ::std::option::Option<::std::string::String>,
pub(crate) branch_key_version: ::std::option::Option<::std::string::String>,
}
impl GetBranchKeyVersionInputBuilder {
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
#[allow(missing_docs)] // documentation missing in model
pub fn branch_key_version(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.branch_key_version = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_branch_key_version(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.branch_key_version = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_branch_key_version(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_version
}
    /// Consumes the builder and constructs a [`GetBranchKeyVersionInput`](crate::operation::operation::GetBranchKeyVersionInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::operation::get_branch_key_version::GetBranchKeyVersionInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_keyStore::operation::get_branch_key_version::GetBranchKeyVersionInput {
            branch_key_identifier: self.branch_key_identifier,
branch_key_version: self.branch_key_version,
        })
    }
}
