// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::ExportSummary,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExportSummary>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExportSummary::ExportSummary {
        ExportArn: crate::standard_library_conversions::ostring_to_dafny(&value.export_arn),
 ExportStatus: ::std::rc::Rc::new(match &value.export_status {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_dynamodb::conversions::export_status::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExportSummary,
    >,
) -> aws_sdk_dynamodb::types::ExportSummary {
    aws_sdk_dynamodb::types::ExportSummary::builder()
          .set_export_arn(crate::standard_library_conversions::ostring_from_dafny(dafny_value.ExportArn().clone()))
 .set_export_status(match &**dafny_value.ExportStatus() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::deps::com_amazonaws_dynamodb::conversions::export_status::from_dafny(value)
    ),
    _ => None,
}
)
          .build()

}
