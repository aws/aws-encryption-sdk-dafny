// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct CreateRequiredEncryptionContextCmmInput {
    #[allow(missing_docs)] // documentation missing in model
pub keyring: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>,
#[allow(missing_docs)] // documentation missing in model
pub required_encryption_context_keys: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub underlying_cmm: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef>,
}
impl CreateRequiredEncryptionContextCmmInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn keyring(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef> {
    &self.keyring
}
#[allow(missing_docs)] // documentation missing in model
pub fn required_encryption_context_keys(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.required_encryption_context_keys
}
#[allow(missing_docs)] // documentation missing in model
pub fn underlying_cmm(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef> {
    &self.underlying_cmm
}
}
impl CreateRequiredEncryptionContextCmmInput {
    /// Creates a new builder-style object to manufacture [`CreateRequiredEncryptionContextCmmInput`](crate::operation::create_required_encryption_context_cmm::builders::CreateRequiredEncryptionContextCmmInput).
    pub fn builder() -> crate::deps::aws_cryptography_materialProviders::operation::create_required_encryption_context_cmm::builders::CreateRequiredEncryptionContextCmmInputBuilder {
        crate::deps::aws_cryptography_materialProviders::operation::create_required_encryption_context_cmm::builders::CreateRequiredEncryptionContextCmmInputBuilder::default()
    }
}

/// A builder for [`CreateRequiredEncryptionContextCmmInput`](crate::operation::operation::CreateRequiredEncryptionContextCmmInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct CreateRequiredEncryptionContextCmmInputBuilder {
    pub(crate) keyring: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>,
pub(crate) required_encryption_context_keys: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) underlying_cmm: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef>,
}
impl CreateRequiredEncryptionContextCmmInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn keyring(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>) -> Self {
    self.keyring = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_keyring(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef>) -> Self {
    self.keyring = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_keyring(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef> {
    &self.keyring
}
#[allow(missing_docs)] // documentation missing in model
pub fn required_encryption_context_keys(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.required_encryption_context_keys = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_required_encryption_context_keys(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.required_encryption_context_keys = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_required_encryption_context_keys(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.required_encryption_context_keys
}
#[allow(missing_docs)] // documentation missing in model
pub fn underlying_cmm(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef>) -> Self {
    self.underlying_cmm = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_underlying_cmm(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef>) -> Self {
    self.underlying_cmm = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_underlying_cmm(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::cryptographic_materials_manager::CryptographicMaterialsManagerRef> {
    &self.underlying_cmm
}
    /// Consumes the builder and constructs a [`CreateRequiredEncryptionContextCmmInput`](crate::operation::operation::CreateRequiredEncryptionContextCmmInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::operation::create_required_encryption_context_cmm::CreateRequiredEncryptionContextCmmInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_materialProviders::operation::create_required_encryption_context_cmm::CreateRequiredEncryptionContextCmmInput {
            keyring: self.keyring,
required_encryption_context_keys: self.required_encryption_context_keys,
underlying_cmm: self.underlying_cmm,
        })
    }
}
