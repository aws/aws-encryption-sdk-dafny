// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::sign::SignError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::sign::SignError::DependencyTimeoutException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::DisabledException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::disabled_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::DryRunOperationException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::dry_run_operation_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::InvalidGrantTokenException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_grant_token_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::InvalidKeyUsageException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::invalid_key_usage_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::KeyUnavailableException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::key_unavailable_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::KmsInternalException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::KmsInvalidStateException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::sign::SignError::NotFoundException(e) =>
            crate::deps::com_amazonaws_kms::conversions::error::not_found_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_kms::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _sign_request;

 pub mod _sign_response;
