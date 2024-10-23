// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::DeleteReplicaAction,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DeleteReplicaAction>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DeleteReplicaAction::DeleteReplicaAction {
        RegionName: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.region_name),
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DeleteReplicaAction,
    >,
) -> aws_sdk_dynamodb::types::DeleteReplicaAction {
    aws_sdk_dynamodb::types::DeleteReplicaAction::builder()
          .set_region_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.RegionName()) ))
          .build()
          .unwrap()
}
