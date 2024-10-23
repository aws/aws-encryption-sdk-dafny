// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::revoke_grant::RevokeGrantInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RevokeGrantRequest,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RevokeGrantRequest::RevokeGrantRequest {
        KeyId: crate::standard_library_conversions::ostring_to_dafny(&value.key_id) .Extract(),
 GrantId: crate::standard_library_conversions::ostring_to_dafny(&value.grant_id) .Extract(),
 DryRun: crate::standard_library_conversions::obool_to_dafny(&value.dry_run),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RevokeGrantRequest,
    >
) -> aws_sdk_kms::operation::revoke_grant::RevokeGrantInput {
    aws_sdk_kms::operation::revoke_grant::RevokeGrantInput::builder()
          .set_key_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.KeyId()) ))
 .set_grant_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.GrantId()) ))
 .set_dry_run(crate::standard_library_conversions::obool_from_dafny(dafny_value.DryRun().clone()))
          .build()
          .unwrap()
}
