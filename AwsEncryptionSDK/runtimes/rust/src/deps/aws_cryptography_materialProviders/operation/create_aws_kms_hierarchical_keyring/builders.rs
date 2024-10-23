// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::_create_keyring_output::CreateKeyringOutputBuilder;

pub use crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::_create_aws_kms_hierarchical_keyring_input::CreateAwsKmsHierarchicalKeyringInputBuilder;

impl CreateAwsKmsHierarchicalKeyringInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        let mut fluent_builder = client.create_aws_kms_hierarchical_keyring();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `CreateAwsKmsHierarchicalKeyring`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct CreateAwsKmsHierarchicalKeyringFluentBuilder {
    client: crate::deps::aws_cryptography_materialProviders::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::builders::CreateAwsKmsHierarchicalKeyringInputBuilder,
}
impl CreateAwsKmsHierarchicalKeyringFluentBuilder {
    /// Creates a new `CreateAwsKmsHierarchicalKeyring`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_materialProviders::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the CreateAwsKmsHierarchicalKeyring as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::builders::CreateAwsKmsHierarchicalKeyringInputBuilder {
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
        crate::deps::aws_cryptography_materialProviders::operation::create_aws_kms_hierarchical_keyring::CreateAwsKmsHierarchicalKeyring::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn branch_key_id(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.branch_key_id(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_branch_key_id(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_branch_key_id(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_branch_key_id(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_branch_key_id()
}
#[allow(missing_docs)] // documentation missing in model
pub fn branch_key_id_supplier(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::branch_key_id_supplier::BranchKeyIdSupplierRef>) -> Self {
    self.inner = self.inner.branch_key_id_supplier(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_branch_key_id_supplier(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::branch_key_id_supplier::BranchKeyIdSupplierRef>) -> Self {
    self.inner = self.inner.set_branch_key_id_supplier(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_branch_key_id_supplier(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::branch_key_id_supplier::BranchKeyIdSupplierRef> {
    self.inner.get_branch_key_id_supplier()
}
#[allow(missing_docs)] // documentation missing in model
pub fn cache(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::CacheType>) -> Self {
    self.inner = self.inner.cache(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_cache(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::CacheType>) -> Self {
    self.inner = self.inner.set_cache(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_cache(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::CacheType> {
    self.inner.get_cache()
}
#[allow(missing_docs)] // documentation missing in model
pub fn key_store(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_keyStore::client::Client>) -> Self {
    self.inner = self.inner.key_store(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_key_store(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_keyStore::client::Client>) -> Self {
    self.inner = self.inner.set_key_store(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_key_store(&self) -> &::std::option::Option<crate::deps::aws_cryptography_keyStore::client::Client> {
    self.inner.get_key_store()
}
#[allow(missing_docs)] // documentation missing in model
pub fn partition_id(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.partition_id(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_partition_id(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_partition_id(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_partition_id(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_partition_id()
}
#[allow(missing_docs)] // documentation missing in model
pub fn ttl_seconds(mut self, input: impl ::std::convert::Into<::std::primitive::i64>) -> Self {
    self.inner = self.inner.ttl_seconds(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_ttl_seconds(mut self, input: ::std::option::Option<::std::primitive::i64>) -> Self {
    self.inner = self.inner.set_ttl_seconds(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_ttl_seconds(&self) -> &::std::option::Option<::std::primitive::i64> {
    self.inner.get_ttl_seconds()
}
}
