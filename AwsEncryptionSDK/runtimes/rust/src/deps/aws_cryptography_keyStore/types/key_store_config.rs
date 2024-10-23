// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct KeyStoreConfig {
    #[allow(missing_docs)] // documentation missing in model
pub ddb_client: ::std::option::Option<crate::deps::com_amazonaws_dynamodb::client::Client>,
#[allow(missing_docs)] // documentation missing in model
pub ddb_table_name: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub id: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub kms_client: ::std::option::Option<crate::deps::com_amazonaws_kms::client::Client>,
#[allow(missing_docs)] // documentation missing in model
pub kms_configuration: ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration>,
#[allow(missing_docs)] // documentation missing in model
pub logical_key_store_name: ::std::option::Option<::std::string::String>,
}
impl KeyStoreConfig {
    #[allow(missing_docs)] // documentation missing in model
pub fn ddb_client(&self) -> &::std::option::Option<crate::deps::com_amazonaws_dynamodb::client::Client> {
    &self.ddb_client
}
#[allow(missing_docs)] // documentation missing in model
pub fn ddb_table_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.ddb_table_name
}
#[allow(missing_docs)] // documentation missing in model
pub fn grant_tokens(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.grant_tokens
}
#[allow(missing_docs)] // documentation missing in model
pub fn id(&self) -> &::std::option::Option<::std::string::String> {
    &self.id
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_client(&self) -> &::std::option::Option<crate::deps::com_amazonaws_kms::client::Client> {
    &self.kms_client
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_configuration(&self) -> &::std::option::Option<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration> {
    &self.kms_configuration
}
#[allow(missing_docs)] // documentation missing in model
pub fn logical_key_store_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.logical_key_store_name
}
}
impl KeyStoreConfig {
    /// Creates a new builder-style object to manufacture [`KeyStoreConfig`](crate::deps::aws_cryptography_keyStore::types::KeyStoreConfig).
    pub fn builder() -> crate::deps::aws_cryptography_keyStore::types::key_store_config::KeyStoreConfigBuilder {
        crate::deps::aws_cryptography_keyStore::types::key_store_config::KeyStoreConfigBuilder::default()
    }
}

/// A builder for [`KeyStoreConfig`](crate::deps::aws_cryptography_keyStore::types::KeyStoreConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct KeyStoreConfigBuilder {
    pub(crate) ddb_client: ::std::option::Option<crate::deps::com_amazonaws_dynamodb::client::Client>,
pub(crate) ddb_table_name: ::std::option::Option<::std::string::String>,
pub(crate) grant_tokens: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) id: ::std::option::Option<::std::string::String>,
pub(crate) kms_client: ::std::option::Option<crate::deps::com_amazonaws_kms::client::Client>,
pub(crate) kms_configuration: ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration>,
pub(crate) logical_key_store_name: ::std::option::Option<::std::string::String>,
}
impl KeyStoreConfigBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn ddb_client(mut self, input: impl ::std::convert::Into<crate::deps::com_amazonaws_dynamodb::client::Client>) -> Self {
    self.ddb_client = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_ddb_client(mut self, input: ::std::option::Option<crate::deps::com_amazonaws_dynamodb::client::Client>) -> Self {
    self.ddb_client = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_ddb_client(&self) -> &::std::option::Option<crate::deps::com_amazonaws_dynamodb::client::Client> {
    &self.ddb_client
}
#[allow(missing_docs)] // documentation missing in model
pub fn ddb_table_name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.ddb_table_name = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_ddb_table_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.ddb_table_name = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_ddb_table_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.ddb_table_name
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
pub fn id(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.id = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_id(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.id = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_id(&self) -> &::std::option::Option<::std::string::String> {
    &self.id
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
pub fn kms_configuration(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration>) -> Self {
    self.kms_configuration = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_kms_configuration(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration>) -> Self {
    self.kms_configuration = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_kms_configuration(&self) -> &::std::option::Option<crate::deps::aws_cryptography_keyStore::types::KmsConfiguration> {
    &self.kms_configuration
}
#[allow(missing_docs)] // documentation missing in model
pub fn logical_key_store_name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.logical_key_store_name = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_logical_key_store_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.logical_key_store_name = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_logical_key_store_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.logical_key_store_name
}
    /// Consumes the builder and constructs a [`KeyStoreConfig`](crate::deps::aws_cryptography_keyStore::types::KeyStoreConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::types::key_store_config::KeyStoreConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_keyStore::types::key_store_config::KeyStoreConfig {
            ddb_client: self.ddb_client,
ddb_table_name: self.ddb_table_name,
grant_tokens: self.grant_tokens,
id: self.id,
kms_client: self.kms_client,
kms_configuration: self.kms_configuration,
logical_key_store_name: self.logical_key_store_name,
        })
    }
}
