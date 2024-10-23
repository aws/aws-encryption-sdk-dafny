// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SingleThreadedCache {
    #[allow(missing_docs)] // documentation missing in model
pub entry_capacity: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub entry_pruning_tail_size: ::std::option::Option<::std::primitive::i32>,
}
impl SingleThreadedCache {
    #[allow(missing_docs)] // documentation missing in model
pub fn entry_capacity(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_capacity
}
#[allow(missing_docs)] // documentation missing in model
pub fn entry_pruning_tail_size(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_pruning_tail_size
}
}
impl SingleThreadedCache {
    /// Creates a new builder-style object to manufacture [`SingleThreadedCache`](crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::SingleThreadedCacheBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::SingleThreadedCacheBuilder::default()
    }
}

/// A builder for [`SingleThreadedCache`](crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SingleThreadedCacheBuilder {
    pub(crate) entry_capacity: ::std::option::Option<::std::primitive::i32>,
pub(crate) entry_pruning_tail_size: ::std::option::Option<::std::primitive::i32>,
}
impl SingleThreadedCacheBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn entry_capacity(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.entry_capacity = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_entry_capacity(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.entry_capacity = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_entry_capacity(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_capacity
}
#[allow(missing_docs)] // documentation missing in model
pub fn entry_pruning_tail_size(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.entry_pruning_tail_size = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_entry_pruning_tail_size(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.entry_pruning_tail_size = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_entry_pruning_tail_size(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_pruning_tail_size
}
    /// Consumes the builder and constructs a [`SingleThreadedCache`](crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache {
            entry_capacity: self.entry_capacity,
entry_pruning_tail_size: self.entry_pruning_tail_size,
        })
    }
}
