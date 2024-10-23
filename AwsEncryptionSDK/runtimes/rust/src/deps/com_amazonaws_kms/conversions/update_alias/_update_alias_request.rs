// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::update_alias::UpdateAliasInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateAliasRequest,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateAliasRequest::UpdateAliasRequest {
        AliasName: crate::standard_library_conversions::ostring_to_dafny(&value.alias_name) .Extract(),
 TargetKeyId: crate::standard_library_conversions::ostring_to_dafny(&value.target_key_id) .Extract(),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateAliasRequest,
    >
) -> aws_sdk_kms::operation::update_alias::UpdateAliasInput {
    aws_sdk_kms::operation::update_alias::UpdateAliasInput::builder()
          .set_alias_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.AliasName()) ))
 .set_target_key_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.TargetKeyId()) ))
          .build()
          .unwrap()
}
