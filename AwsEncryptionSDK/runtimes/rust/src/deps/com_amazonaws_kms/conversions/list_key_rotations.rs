// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::InvalidArnException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_arn_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::InvalidMarkerException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_marker_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::KmsInternalException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::KmsInvalidStateException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::NotFoundException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsError::UnsupportedOperationException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::unsupported_operation_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _list_key_rotations_request;

 pub mod _list_key_rotations_response;
