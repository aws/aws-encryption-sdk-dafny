// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::DependencyTimeoutException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::ExpiredImportTokenException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::expired_import_token_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::IncorrectKeyMaterialException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::incorrect_key_material_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::InvalidArnException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_arn_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::InvalidCiphertextException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_ciphertext_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::InvalidImportTokenException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_import_token_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::KmsInternalException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::KmsInvalidStateException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::NotFoundException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::import_key_material::ImportKeyMaterialError::UnsupportedOperationException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::unsupported_operation_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _import_key_material_request;

 pub mod _import_key_material_response;
