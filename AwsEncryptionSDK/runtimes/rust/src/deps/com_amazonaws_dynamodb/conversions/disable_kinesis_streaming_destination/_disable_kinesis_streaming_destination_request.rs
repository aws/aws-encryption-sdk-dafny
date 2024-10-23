// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DisableKinesisStreamingDestinationInput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DisableKinesisStreamingDestinationInput::DisableKinesisStreamingDestinationInput {
        TableName: crate::standard_library_conversions::ostring_to_dafny(&value.table_name) .Extract(),
 StreamArn: crate::standard_library_conversions::ostring_to_dafny(&value.stream_arn) .Extract(),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DisableKinesisStreamingDestinationInput,
    >
) -> aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationInput {
    aws_sdk_dynamodb::operation::disable_kinesis_streaming_destination::DisableKinesisStreamingDestinationInput::builder()
          .set_table_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.TableName()) ))
 .set_stream_arn(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.StreamArn()) ))
          .build()
          .unwrap()
}
