// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::deps::aws_cryptography_materialProviders::client::Client {
    /// Constructs a fluent builder for the [`InitializeEncryptionMaterials`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`algorithm_suite_id(impl Into<Option<crate::deps::aws_cryptography_materialProviders::types::AlgorithmSuiteId>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::algorithm_suite_id) / [`set_algorithm_suite_id(Option<crate::deps::aws_cryptography_materialProviders::types::AlgorithmSuiteId>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::set_algorithm_suite_id): (undocumented)<br>
    ///   - [`encryption_context(impl Into<Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::encryption_context) / [`set_encryption_context(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::set_encryption_context): (undocumented)<br>
    ///   - [`required_encryption_context_keys(impl Into<Option<::std::vec::Vec<::std::string::String>>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::required_encryption_context_keys) / [`set_required_encryption_context_keys(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::set_required_encryption_context_keys): (undocumented)<br>
    ///   - [`signing_key(impl Into<Option<::aws_smithy_types::Blob>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::signing_key) / [`set_signing_key(Option<::aws_smithy_types::Blob>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::set_signing_key): (undocumented)<br>
    ///   - [`verification_key(impl Into<Option<::aws_smithy_types::Blob>>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::verification_key) / [`set_verification_key(Option<::aws_smithy_types::Blob>)`](crate::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::set_verification_key): (undocumented)<br>
    /// - On success, responds with [`EncryptionMaterials`](crate::operation::initialize_encryption_materials::EncryptionMaterials) with field(s):
    ///   - [`algorithm_suite(Option<crate::deps::aws_cryptography_materialProviders::types::AlgorithmSuiteInfo>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::algorithm_suite): (undocumented)
    ///   - [`encrypted_data_keys(Option<::std::vec::Vec<crate::deps::aws_cryptography_materialProviders::types::EncryptedDataKey>>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::encrypted_data_keys): (undocumented)
    ///   - [`encryption_context(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::encryption_context): (undocumented)
    ///   - [`plaintext_data_key(Option<::aws_smithy_types::Blob>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::plaintext_data_key): (undocumented)
    ///   - [`required_encryption_context_keys(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::required_encryption_context_keys): (undocumented)
    ///   - [`signing_key(Option<::aws_smithy_types::Blob>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::signing_key): (undocumented)
    ///   - [`symmetric_signing_keys(Option<::std::vec::Vec<::aws_smithy_types::Blob>>)`](crate::operation::initialize_encryption_materials::EncryptionMaterials::symmetric_signing_keys): (undocumented)
    /// - On failure, responds with [`SdkError<InitializeEncryptionMaterialsError>`](crate::operation::initialize_encryption_materials::InitializeEncryptionMaterialsError)
    pub fn initialize_encryption_materials(&self) -> crate::deps::aws_cryptography_materialProviders::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder {
        crate::deps::aws_cryptography_materialProviders::operation::initialize_encryption_materials::builders::InitializeEncryptionMaterialsFluentBuilder::new(self.clone())
    }
}
