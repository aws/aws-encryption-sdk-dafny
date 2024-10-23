// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_keyStore::operation::create_key_store::_create_key_store_output::CreateKeyStoreOutputBuilder;

pub use crate::deps::aws_cryptography_keyStore::operation::create_key_store::_create_key_store_input::CreateKeyStoreInputBuilder;

impl CreateKeyStoreInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_keyStore::client::Client,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::operation::create_key_store::CreateKeyStoreOutput,
        crate::deps::aws_cryptography_keyStore::types::error::Error,
    > {
        let mut fluent_builder = client.create_key_store();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `CreateKeyStore`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct CreateKeyStoreFluentBuilder {
    client: crate::deps::aws_cryptography_keyStore::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_keyStore::operation::create_key_store::builders::CreateKeyStoreInputBuilder,
}
impl CreateKeyStoreFluentBuilder {
    /// Creates a new `CreateKeyStore`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_keyStore::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the CreateKeyStore as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_keyStore::operation::create_key_store::builders::CreateKeyStoreInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_keyStore::operation::create_key_store::CreateKeyStoreOutput,
        crate::deps::aws_cryptography_keyStore::types::error::Error,
    > {
        let input = self
            .inner
            .build()
            // Using Opaque since we don't have a validation-specific error yet.
            // Operations' models don't declare their own validation error,
            // and smithy-rs seems to not generate a ValidationError case unless there is.
            // Vanilla smithy-rs uses SdkError::construction_failure, but we aren't using SdkError.
            .map_err(|mut e| crate::deps::aws_cryptography_keyStore::types::error::Error::Opaque {
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any),
		alt_text : format!("{:?}", e)
            })?;
        crate::deps::aws_cryptography_keyStore::operation::create_key_store::CreateKeyStore::send(&self.client, input).await
    }


}
