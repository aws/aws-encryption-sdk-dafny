// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error> {
    match value {
      aws_sdk_dynamodb::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::InternalServerError(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::internal_server_error::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::InvalidEndpointException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::invalid_endpoint_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::ProvisionedThroughputExceededException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::provisioned_throughput_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::RequestLimitExceeded(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::request_limit_exceeded::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::ResourceNotFoundException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::resource_not_found_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::transact_get_items::TransactGetItemsError::TransactionCanceledException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::transaction_canceled_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _transact_get_items_request;

 pub mod _transact_get_items_response;
