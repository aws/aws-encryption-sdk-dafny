// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::aws_cryptography_materialProviders::operation::valid_decryption_materials_transition::_unit::UnitBuilder;

pub use crate::deps::aws_cryptography_materialProviders::operation::valid_decryption_materials_transition::_valid_decryption_materials_transition_input::ValidDecryptionMaterialsTransitionInputBuilder;

impl ValidDecryptionMaterialsTransitionInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::aws_cryptography_materialProviders::client::Client,
    ) -> ::std::result::Result<
        (),
        crate::deps::aws_cryptography_materialProviders::types::error::Error,
    > {
        let mut fluent_builder = client.valid_decryption_materials_transition();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `ValidDecryptionMaterialsTransition`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct ValidDecryptionMaterialsTransitionFluentBuilder {
    client: crate::deps::aws_cryptography_materialProviders::client::Client,
    pub(crate) inner: crate::deps::aws_cryptography_materialProviders::operation::valid_decryption_materials_transition::builders::ValidDecryptionMaterialsTransitionInputBuilder,
}
impl ValidDecryptionMaterialsTransitionFluentBuilder {
    /// Creates a new `ValidDecryptionMaterialsTransition`.
    pub(crate) fn new(client: crate::deps::aws_cryptography_materialProviders::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the ValidDecryptionMaterialsTransition as a reference.
    pub fn as_input(&self) -> &crate::deps::aws_cryptography_materialProviders::operation::valid_decryption_materials_transition::builders::ValidDecryptionMaterialsTransitionInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        (),
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
        crate::deps::aws_cryptography_materialProviders::operation::valid_decryption_materials_transition::ValidDecryptionMaterialsTransition::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn start(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials>) -> Self {
    self.inner = self.inner.start(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_start(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials>) -> Self {
    self.inner = self.inner.set_start(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_start(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials> {
    self.inner.get_start()
}
#[allow(missing_docs)] // documentation missing in model
pub fn stop(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials>) -> Self {
    self.inner = self.inner.stop(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_stop(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials>) -> Self {
    self.inner = self.inner.set_stop(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_stop(&self) -> &::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::DecryptionMaterials> {
    self.inner.get_stop()
}
}
