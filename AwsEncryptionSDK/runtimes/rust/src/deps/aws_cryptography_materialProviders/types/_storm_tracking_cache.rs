// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct StormTrackingCache {
    #[allow(missing_docs)] // documentation missing in model
pub entry_capacity: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub entry_pruning_tail_size: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub fan_out: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub grace_interval: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub grace_period: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub in_flight_ttl: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub sleep_milli: ::std::option::Option<::std::primitive::i32>,
}
impl StormTrackingCache {
    #[allow(missing_docs)] // documentation missing in model
pub fn entry_capacity(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_capacity
}
#[allow(missing_docs)] // documentation missing in model
pub fn entry_pruning_tail_size(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.entry_pruning_tail_size
}
#[allow(missing_docs)] // documentation missing in model
pub fn fan_out(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.fan_out
}
#[allow(missing_docs)] // documentation missing in model
pub fn grace_interval(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.grace_interval
}
#[allow(missing_docs)] // documentation missing in model
pub fn grace_period(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.grace_period
}
#[allow(missing_docs)] // documentation missing in model
pub fn in_flight_ttl(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.in_flight_ttl
}
#[allow(missing_docs)] // documentation missing in model
pub fn sleep_milli(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.sleep_milli
}
}
impl StormTrackingCache {
    /// Creates a new builder-style object to manufacture [`StormTrackingCache`](crate::deps::aws_cryptography_materialProviders::types::StormTrackingCache).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::types::builders::StormTrackingCacheBuilder {
        crate::deps::aws_cryptography_materialProviders::types::builders::StormTrackingCacheBuilder::default()
    }
}

/// A builder for [`StormTrackingCache`](crate::deps::aws_cryptography_materialProviders::types::StormTrackingCache).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct StormTrackingCacheBuilder {
    pub(crate) entry_capacity: ::std::option::Option<::std::primitive::i32>,
pub(crate) entry_pruning_tail_size: ::std::option::Option<::std::primitive::i32>,
pub(crate) fan_out: ::std::option::Option<::std::primitive::i32>,
pub(crate) grace_interval: ::std::option::Option<::std::primitive::i32>,
pub(crate) grace_period: ::std::option::Option<::std::primitive::i32>,
pub(crate) in_flight_ttl: ::std::option::Option<::std::primitive::i32>,
pub(crate) sleep_milli: ::std::option::Option<::std::primitive::i32>,
}
impl StormTrackingCacheBuilder {
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
#[allow(missing_docs)] // documentation missing in model
pub fn fan_out(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.fan_out = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_fan_out(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.fan_out = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_fan_out(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.fan_out
}
#[allow(missing_docs)] // documentation missing in model
pub fn grace_interval(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.grace_interval = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_grace_interval(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.grace_interval = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_grace_interval(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.grace_interval
}
#[allow(missing_docs)] // documentation missing in model
pub fn grace_period(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.grace_period = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_grace_period(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.grace_period = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_grace_period(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.grace_period
}
#[allow(missing_docs)] // documentation missing in model
pub fn in_flight_ttl(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.in_flight_ttl = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_in_flight_ttl(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.in_flight_ttl = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_in_flight_ttl(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.in_flight_ttl
}
#[allow(missing_docs)] // documentation missing in model
pub fn sleep_milli(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.sleep_milli = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_sleep_milli(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.sleep_milli = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_sleep_milli(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.sleep_milli
}
    /// Consumes the builder and constructs a [`StormTrackingCache`](crate::deps::aws_cryptography_materialProviders::types::StormTrackingCache).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::StormTrackingCache,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::types::StormTrackingCache {
            entry_capacity: self.entry_capacity,
entry_pruning_tail_size: self.entry_pruning_tail_size,
fan_out: self.fan_out,
grace_interval: self.grace_interval,
grace_period: self.grace_period,
in_flight_ttl: self.in_flight_ttl,
sleep_milli: self.sleep_milli,
        })
    }
}
