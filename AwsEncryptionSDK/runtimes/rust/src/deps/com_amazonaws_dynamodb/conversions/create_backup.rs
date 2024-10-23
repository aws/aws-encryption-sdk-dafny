// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_dynamodb::operation::create_backup::CreateBackupError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error> {
    match value {
      aws_sdk_dynamodb::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_dynamodb::operation::create_backup::CreateBackupError::BackupInUseException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::backup_in_use_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::ContinuousBackupsUnavailableException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::continuous_backups_unavailable_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::InternalServerError(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::internal_server_error::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::InvalidEndpointException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::invalid_endpoint_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::LimitExceededException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::TableInUseException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::table_in_use_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::create_backup::CreateBackupError::TableNotFoundException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::table_not_found_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _create_backup_request;

 pub mod _create_backup_response;
