// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::UpdateGlobalSecondaryIndexAction,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateGlobalSecondaryIndexAction>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateGlobalSecondaryIndexAction::UpdateGlobalSecondaryIndexAction {
        IndexName: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.index_name),
 ProvisionedThroughput: crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput::to_dafny(&value.provisioned_throughput.clone().unwrap())
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateGlobalSecondaryIndexAction,
    >,
) -> aws_sdk_dynamodb::types::UpdateGlobalSecondaryIndexAction {
    aws_sdk_dynamodb::types::UpdateGlobalSecondaryIndexAction::builder()
          .set_index_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.IndexName()) ))
 .set_provisioned_throughput(Some( crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput::from_dafny(dafny_value.ProvisionedThroughput().clone())
 ))
          .build()
          .unwrap()
}
