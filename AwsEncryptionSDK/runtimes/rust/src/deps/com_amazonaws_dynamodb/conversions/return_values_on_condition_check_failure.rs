// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure>{
    ::std::rc::Rc::new(match value {
        aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure::AllOld => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure::ALL_OLD {},
aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure::None => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure::NONE {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure,
) -> aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure {
    match dafny_value {
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure::ALL_OLD {} => aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure::AllOld,
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValuesOnConditionCheckFailure::NONE {} => aws_sdk_dynamodb::types::ReturnValuesOnConditionCheckFailure::None,
    }
}
