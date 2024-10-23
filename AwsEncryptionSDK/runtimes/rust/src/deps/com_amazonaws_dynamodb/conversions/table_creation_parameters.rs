// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::TableCreationParameters,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TableCreationParameters>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TableCreationParameters::TableCreationParameters {
        TableName: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.table_name),
 AttributeDefinitions: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&value.attribute_definitions,
    |e| crate::deps::com_amazonaws_dynamodb::conversions::attribute_definition::to_dafny(e)
,
)
,
 KeySchema: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&value.key_schema,
    |e| crate::deps::com_amazonaws_dynamodb::conversions::key_schema_element::to_dafny(e)
,
)
,
 BillingMode: ::std::rc::Rc::new(match &value.billing_mode {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::billing_mode::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 ProvisionedThroughput: ::std::rc::Rc::new(match &value.provisioned_throughput {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput::to_dafny(x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 SSESpecification: ::std::rc::Rc::new(match &value.sse_specification {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::sse_specification::to_dafny(x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 GlobalSecondaryIndexes: ::std::rc::Rc::new(match &value.global_secondary_indexes {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::deps::com_amazonaws_dynamodb::conversions::global_secondary_index::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TableCreationParameters,
    >,
) -> aws_sdk_dynamodb::types::TableCreationParameters {
    aws_sdk_dynamodb::types::TableCreationParameters::builder()
          .set_table_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.TableName()) ))
 .set_attribute_definitions(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(dafny_value.AttributeDefinitions(),
    |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeDefinition>| crate::deps::com_amazonaws_dynamodb::conversions::attribute_definition::from_dafny(e.clone())
,
)
 ))
 .set_key_schema(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(dafny_value.KeySchema(),
    |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::KeySchemaElement>| crate::deps::com_amazonaws_dynamodb::conversions::key_schema_element::from_dafny(e.clone())
,
)
 ))
 .set_billing_mode(match &**dafny_value.BillingMode() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::deps::com_amazonaws_dynamodb::conversions::billing_mode::from_dafny(value)
    ),
    _ => None,
}
)
 .set_provisioned_throughput(match (*dafny_value.ProvisionedThroughput()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::deps::com_amazonaws_dynamodb::conversions::provisioned_throughput::from_dafny(value.clone())),
    _ => None,
}
)
 .set_sse_specification(match (*dafny_value.SSESpecification()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::deps::com_amazonaws_dynamodb::conversions::sse_specification::from_dafny(value.clone())),
    _ => None,
}
)
 .set_global_secondary_indexes(match (*dafny_value.GlobalSecondaryIndexes()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::GlobalSecondaryIndex>| crate::deps::com_amazonaws_dynamodb::conversions::global_secondary_index::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
          .build()
          .unwrap()
}
