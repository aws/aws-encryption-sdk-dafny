// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::list_global_tables::ListGlobalTablesOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ListGlobalTablesOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ListGlobalTablesOutput::ListGlobalTablesOutput {
        GlobalTables: ::std::rc::Rc::new(match &value.global_tables {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::deps::com_amazonaws_dynamodb::conversions::global_table::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 LastEvaluatedGlobalTableName: crate::standard_library_conversions::ostring_to_dafny(&value.last_evaluated_global_table_name),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ListGlobalTablesOutput,
    >
) -> aws_sdk_dynamodb::operation::list_global_tables::ListGlobalTablesOutput {
    aws_sdk_dynamodb::operation::list_global_tables::ListGlobalTablesOutput::builder()
          .set_global_tables(match (*dafny_value.GlobalTables()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::GlobalTable>| crate::deps::com_amazonaws_dynamodb::conversions::global_table::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
 .set_last_evaluated_global_table_name(crate::standard_library_conversions::ostring_from_dafny(dafny_value.LastEvaluatedGlobalTableName().clone()))
          .build()


}
