// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::BatchStatementRequest,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchStatementRequest>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchStatementRequest::BatchStatementRequest {
        Statement: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.statement),
 Parameters: ::std::rc::Rc::new(match &value.parameters {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::deps::com_amazonaws_dynamodb::conversions::attribute_value::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 ConsistentRead: crate::standard_library_conversions::obool_to_dafny(&value.consistent_read),
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchStatementRequest,
    >,
) -> aws_sdk_dynamodb::types::BatchStatementRequest {
    aws_sdk_dynamodb::types::BatchStatementRequest::builder()
          .set_statement(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.Statement()) ))
 .set_parameters(match (*dafny_value.Parameters()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>| crate::deps::com_amazonaws_dynamodb::conversions::attribute_value::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
 .set_consistent_read(crate::standard_library_conversions::obool_from_dafny(dafny_value.ConsistentRead().clone()))
          .build()
          .unwrap()
}
