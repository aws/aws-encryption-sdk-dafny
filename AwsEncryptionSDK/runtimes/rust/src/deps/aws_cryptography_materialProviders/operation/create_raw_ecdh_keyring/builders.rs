// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_materialProviders::operation::create_raw_ecdh_keyring::_create_keyring_output::CreateKeyringOutputBuilder;

pub use crate::deps::aws_cryptography_materialProviders::operation::create_raw_ecdh_keyring::_create_raw_ecdh_keyring_input::CreateRawEcdhKeyringInputBuilder;

impl CreateRawEcdhKeyringInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_materialProviders::types::keyring::KeyringRef,
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        let mut fluent_builder = client.create_raw_ecdh_keyring();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `CreateRawEcdhKeyring`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct CreateRawEcdhKeyringFluentBuilder {
    client: crate::deps::aws_cryptography_materialProviders::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_materialProviders::operation::create_raw_ecdh_keyring::builders::CreateRawEcdhKeyringInputBuilder,
}
impl CreateRawEcdhKeyringFluentBuilder {
    /// Creates a new `CreateRawEcdhKeyring`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_materialProviders::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the CreateRawEcdhKeyring as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_materialProviders::operation::create_raw_ecdh_keyring::builders::CreateRawEcdhKeyringInputBuilder {
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
        crate::deps::aws_cryptography_materialProviders::operation::create_raw_ecdh_keyring::CreateRawEcdhKeyring::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn key_agreement_scheme(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::RawEcdhStaticConfigurations>) -> Self {
    self.inner = self.inner.key_agreement_scheme(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_key_agreement_scheme(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::RawEcdhStaticConfigurations>) -> Self {
    self.inner = self.inner.set_key_agreement_scheme(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_key_agreement_scheme(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::RawEcdhStaticConfigurations> {
    self.inner.get_key_agreement_scheme()
}
#[allow(missing_docs)] // documentation missing in model
pub fn curve_spec(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>) -> Self {
    self.inner = self.inner.curve_spec(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_curve_spec(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>) -> Self {
    self.inner = self.inner.set_curve_spec(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_curve_spec(&self) -> &::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec> {
    self.inner.get_curve_spec()
}
}
