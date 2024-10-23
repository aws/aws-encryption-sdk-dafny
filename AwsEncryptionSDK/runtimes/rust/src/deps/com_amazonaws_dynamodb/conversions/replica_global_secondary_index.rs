// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::ReplicaGlobalSecondaryIndex,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReplicaGlobalSecondaryIndex>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReplicaGlobalSecondaryIndex::ReplicaGlobalSecondaryIndex {
        IndexName: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.index_name),
 ProvisionedThroughputOverride: ::std::rc::Rc::new(match &value.provisioned_throughput_override {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput_override::to_dafny(x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ReplicaGlobalSecondaryIndex,
    >,
) -> aws_sdk_dynamodb::types::ReplicaGlobalSecondaryIndex {
    aws_sdk_dynamodb::types::ReplicaGlobalSecondaryIndex::builder()
          .set_index_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.IndexName()) ))
 .set_provisioned_throughput_override(match (*dafny_value.ProvisionedThroughputOverride()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput_override::from_dafny(value.clone())),
    _ => None,
}
)
          .build()
          .unwrap()
}
