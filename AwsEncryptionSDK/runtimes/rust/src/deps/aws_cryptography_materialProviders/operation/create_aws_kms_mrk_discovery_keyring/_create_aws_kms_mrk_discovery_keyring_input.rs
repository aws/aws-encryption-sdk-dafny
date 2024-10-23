// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateAwsKmsMrkDiscoveryKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub discovery_filter: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter>,
#[allow(missing_docs)] // documentation missing in model
pub grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub kms_client: ::std::option::Option<crate::deps::com_amazonaws_kms::client::Client>,
#[allow(missing_docs)] // documentation missing in model
pub region: ::std::option::Option<::std::string::String>,
}
impl CreateAwsKmsMrkDiscoveryKeyringInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn discovery_filter(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter> {
    &self.discovery_filter
}
#[allow(missing_docs)] // documentation missing in model
pub fn grant_tokens(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.grant_tokens
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_client(&self) -> &::std::option::Option<crate::deps::com_amazonaws_kms::client::Client> {
    &self.kms_client
}
#[allow(missing_docs)] // documentation missing in model
pub fn region(&self) -> &::std::option::Option<::std::string::String> {
    &self.region
}
}
impl CreateAwsKmsMrkDiscoveryKeyringInput {
    /// Creates a new builder-style object to manufacture [`CreateAwsKmsMrkDiscoveryKeyringInput`](crate::operation::create_aws_kms_mrk_discovery_keyring::builders::CreateAwsKmsMrkDiscoveryKeyringInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_discovery_keyring::builders::CreateAwsKmsMrkDiscoveryKeyringInputBuilder {
        crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_discovery_keyring::builders::CreateAwsKmsMrkDiscoveryKeyringInputBuilder::default()
    }
}

/// A builder for [`CreateAwsKmsMrkDiscoveryKeyringInput`](crate::operation::operation::CreateAwsKmsMrkDiscoveryKeyringInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateAwsKmsMrkDiscoveryKeyringInputBuilder {
    pub(crate) discovery_filter: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter>,
pub(crate) grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) kms_client: ::std::option::Option<crate::deps::com_amazonaws_kms::client::Client>,
pub(crate) region: ::std::option::Option<::std::string::String>,
}
impl CreateAwsKmsMrkDiscoveryKeyringInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn discovery_filter(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter>) -> Self {
    self.discovery_filter = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_discovery_filter(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter>) -> Self {
    self.discovery_filter = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_discovery_filter(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DiscoveryFilter> {
    &self.discovery_filter
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
pub fn kms_client(mut self, input: impl ::std::convert::Into<crate::deps::com_amazonaws_kms::client::Client>) -> Self {
    self.kms_client = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_kms_client(mut self, input: ::std::option::Option<crate::deps::com_amazonaws_kms::client::Client>) -> Self {
    self.kms_client = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_kms_client(&self) -> &::std::option::Option<crate::deps::com_amazonaws_kms::client::Client> {
    &self.kms_client
}
#[allow(missing_docs)] // documentation missing in model
pub fn region(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.region = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_region(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.region = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_region(&self) -> &::std::option::Option<::std::string::String> {
    &self.region
}
    /// Consumes the builder and constructs a [`CreateAwsKmsMrkDiscoveryKeyringInput`](crate::operation::operation::CreateAwsKmsMrkDiscoveryKeyringInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_discovery_keyring::CreateAwsKmsMrkDiscoveryKeyringInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_mrk_discovery_keyring::CreateAwsKmsMrkDiscoveryKeyringInput {
            discovery_filter: self.discovery_filter,
grant_tokens: self.grant_tokens,
kms_client: self.kms_client,
region: self.region,
        })
    }
}
