// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error> {
    match value {
      aws_sdk_dynamodb::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError::InternalServerError(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::internal_server_error::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError::InvalidEndpointException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::invalid_endpoint_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError::LimitExceededException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError::ResourceInUseException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::resource_in_use_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationError::ResourceNotFoundException(e) =>
            crate::deps::com_amazonaws_dynamodb::conversions::error::resource_not_found_exception::to_dafny(e.clone()),
        e => crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", e)),
      },
      _ => {
        crate::deps::com_amazonaws_dynamodb::conversions::error::to_opaque_error(format!("{:?}", value))
      }
   }
}

 pub mod _disable_kinesis_streaming_destination_request;

 pub mod _disable_kinesis_streaming_destination_response;
