// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::describe_table_replica_auto_scaling::DescribeTableReplicaAutoScalingOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableReplicaAutoScalingOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableReplicaAutoScalingOutput::DescribeTableReplicaAutoScalingOutput {
        TableAutoScalingDescription: ::std::rc::Rc::new(match &value.table_auto_scaling_description {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::table_auto_scaling_description::to_dafny(x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableReplicaAutoScalingOutput,
    >
) -> aws_sdk_dynamodb::operation::describe_table_replica_auto_scaling::DescribeTableReplicaAutoScalingOutput {
    aws_sdk_dynamodb::operation::describe_table_replica_auto_scaling::DescribeTableReplicaAutoScalingOutput::builder()
          .set_table_auto_scaling_description(match (*dafny_value.TableAutoScalingDescription()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::deps::com_amazonaws_dynamodb::conversions::table_auto_scaling_description::from_dafny(value.clone())),
    _ => None,
}
)
          .build()


}
