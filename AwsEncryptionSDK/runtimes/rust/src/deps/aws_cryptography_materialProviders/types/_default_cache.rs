// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct DefaultCache {
    #[allow(missing_docs)] // documentation missing in model
pub entry_capacity: ::std::option::Option<::std::primitive::i32>,
}
impl DefaultCache {
    #[allow(missing_docs)] // documentation missing in model
pub fn entry_capacity(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_capacity
}
}
impl DefaultCache {
    /// Creates a new builder-style object to manufacture [`DefaultCache`](crate::deps::aws_cryptography_materialProviders::types::DefaultCache).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::DefaultCacheBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::DefaultCacheBuilder::default()
    }
}

/// A builder for [`DefaultCache`](crate::deps::aws_cryptography_materialProviders::types::DefaultCache).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct DefaultCacheBuilder {
    pub(crate) entry_capacity: ::std::option::Option<::std::primitive::i32>,
}
impl DefaultCacheBuilder {
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
    /// Consumes the builder and constructs a [`DefaultCache`](crate::deps::aws_cryptography_materialProviders::types::DefaultCache).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::DefaultCache,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::DefaultCache {
            entry_capacity: self.entry_capacity,
        })
    }
}
