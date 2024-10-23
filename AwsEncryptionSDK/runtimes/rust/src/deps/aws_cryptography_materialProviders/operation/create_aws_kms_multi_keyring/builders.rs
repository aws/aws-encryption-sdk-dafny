// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_multi_keyring::_create_keyring_output::CreateKeyringOutputBuilder;

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_multi_keyring::_create_aws_kms_multi_keyring_input::CreateAwsKmsMultiKeyringInputBuilder;

impl CreateAwsKmsMultiKeyringInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        let mut fluent_builder = client.create_aws_kms_multi_keyring();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `CreateAwsKmsMultiKeyring`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct CreateAwsKmsMultiKeyringFluentBuilder {
    client: crate::deps::aws_cryptography_materialProviders::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_multi_keyring::builders::CreateAwsKmsMultiKeyringInputBuilder,
}
impl CreateAwsKmsMultiKeyringFluentBuilder {
    /// Creates a new `CreateAwsKmsMultiKeyring`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_materialProviders::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the CreateAwsKmsMultiKeyring as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_multi_keyring::builders::CreateAwsKmsMultiKeyringInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        let input = self
            .inner
            .build()
            // Using Opaque since we don't have a validation-specific error yet.
            // Operations' models don't declare their own validation error,
            // and smithy-rs seems to not generate a ValidationError case unless there is.
            // Vanilla smithy-rs uses SdkError::construction_failure, but we aren't using SdkError.
            .map_err(|mut e| crate::deps::aws_cryptography_materialProviders::types::error::Error::Opaque {
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any),
		alt_text : format!("{:?}", e)
            })?;
        crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_multi_keyring::CreateAwsKmsMultiKeyring::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn client_supplier(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>) -> Self {
    self.inner = self.inner.client_supplier(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_client_supplier(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef>) -> Self {
    self.inner = self.inner.set_client_supplier(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_client_supplier(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::client_supplier::ClientSupplierRef> {
    self.inner.get_client_supplier()
}
#[allow(missing_docs)] // documentation missing in model
pub fn generator(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.generator(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_generator(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_generator(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_generator(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_generator()
}
#[allow(missing_docs)] // documentation missing in model
pub fn grant_tokens(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.grant_tokens(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_grant_tokens(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_grant_tokens(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_grant_tokens(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_grant_tokens()
}
#[allow(missing_docs)] // documentation missing in model
pub fn kms_key_ids(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.kms_key_ids(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_kms_key_ids(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_kms_key_ids(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_kms_key_ids(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_kms_key_ids()
}
}
