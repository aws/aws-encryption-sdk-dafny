// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct DecompressPublicKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub compressed_public_key: ::std::option::Option<::aws_smithy_types::Blob>,
#[allow(missing_docs)] // documentation missing in model
pub ecc_curve: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>,
}
impl DecompressPublicKeyInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn compressed_public_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.compressed_public_key
}
#[allow(missing_docs)] // documentation missing in model
pub fn ecc_curve(&self) -> &::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec> {
    &self.ecc_curve
}
}
impl DecompressPublicKeyInput {
    /// Creates a new builder-style object to manufacture [`DecompressPublicKeyInput`](crate::deps::aws_cryptography_primitives::types::DecompressPublicKeyInput).
    pub fn builder() -> crate::deps::aws_cryptography_primitives::types::builders::DecompressPublicKeyInputBuilder {
        crate::deps::aws_cryptography_primitives::types::builders::DecompressPublicKeyInputBuilder::default()
    }
}

/// A builder for [`DecompressPublicKeyInput`](crate::deps::aws_cryptography_primitives::types::DecompressPublicKeyInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct DecompressPublicKeyInputBuilder {
    pub(crate) compressed_public_key: ::std::option::Option<::aws_smithy_types::Blob>,
pub(crate) ecc_curve: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>,
}
impl DecompressPublicKeyInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn compressed_public_key(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.compressed_public_key = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_compressed_public_key(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.compressed_public_key = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_compressed_public_key(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.compressed_public_key
}
#[allow(missing_docs)] // documentation missing in model
pub fn ecc_curve(mut self, input: impl ::std::convert::Into<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>) -> Self {
    self.ecc_curve = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_ecc_curve(mut self, input: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec>) -> Self {
    self.ecc_curve = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_ecc_curve(&self) -> &::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdhCurveSpec> {
    &self.ecc_curve
}
    /// Consumes the builder and constructs a [`DecompressPublicKeyInput`](crate::deps::aws_cryptography_primitives::types::DecompressPublicKeyInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::deps::aws_cryptography_primitives::types::DecompressPublicKeyInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::deps::aws_cryptography_primitives::types::DecompressPublicKeyInput {
            compressed_public_key: self.compressed_public_key,
ecc_curve: self.ecc_curve,
        })
    }
}
