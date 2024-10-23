// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBranchKeyIdOutput {
    #[allow(missing_docs)] // documentation missing in model
pub branch_key_id: ::std::option::Option<::std::string::String>,
}
impl GetBranchKeyIdOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_id(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_id
}
}
impl GetBranchKeyIdOutput {
    /// Creates a new builder-style object to manufacture [`GetBranchKeyIdOutput`](crate::deps::aws_cryptography_materialProviders::types::GetBranchKeyIdOutput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::GetBranchKeyIdOutputBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::GetBranchKeyIdOutputBuilder::default()
    }
}

/// A builder for [`GetBranchKeyIdOutput`](crate::deps::aws_cryptography_materialProviders::types::GetBranchKeyIdOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBranchKeyIdOutputBuilder {
    pub(crate) branch_key_id: ::std::option::Option<::std::string::String>,
}
impl GetBranchKeyIdOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_id(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.branch_key_id = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_branch_key_id(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.branch_key_id = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_branch_key_id(&self) -> &::std::option::Option<::std::string::String> {
    &self.branch_key_id
}
    /// Consumes the builder and constructs a [`GetBranchKeyIdOutput`](crate::deps::aws_cryptography_materialProviders::types::GetBranchKeyIdOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::GetBranchKeyIdOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::GetBranchKeyIdOutput {
            branch_key_id: self.branch_key_id,
        })
    }
}
