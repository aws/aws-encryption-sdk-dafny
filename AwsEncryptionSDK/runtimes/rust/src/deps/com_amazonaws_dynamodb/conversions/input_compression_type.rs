// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::InputCompressionType,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType>{
    ::std::rc::Rc::new(match value {
        aws_sdk_dynamodb::types::InputCompressionType::Gzip => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::GZIP {},
aws_sdk_dynamodb::types::InputCompressionType::Zstd => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::ZSTD {},
aws_sdk_dynamodb::types::InputCompressionType::None => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::NONE {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType,
) -> aws_sdk_dynamodb::types::InputCompressionType {
    match dafny_value {
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::GZIP {} => aws_sdk_dynamodb::types::InputCompressionType::Gzip,
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::ZSTD {} => aws_sdk_dynamodb::types::InputCompressionType::Zstd,
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::InputCompressionType::NONE {} => aws_sdk_dynamodb::types::InputCompressionType::None,
    }
}
