// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListKeyRotationsResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListKeyRotationsResponse::ListKeyRotationsResponse {
        Rotations: ::std::rc::Rc::new(match &value.rotations {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::deps::com_amazonaws_kms::conversions::rotations_list_entry::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 NextMarker: crate::standard_library_conversions::ostring_to_dafny(&value.next_marker),
 Truncated: crate::standard_library_conversions::obool_to_dafny(&Some(value.truncated)),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListKeyRotationsResponse,
    >
) -> aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsOutput {
    aws_sdk_kms::operation::list_key_rotations::ListKeyRotationsOutput::builder()
          .set_rotations(match (*dafny_value.Rotations()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RotationsListEntry>| crate::deps::com_amazonaws_kms::conversions::rotations_list_entry::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
 .set_next_marker(crate::standard_library_conversions::ostring_from_dafny(dafny_value.NextMarker().clone()))
 .set_truncated(crate::standard_library_conversions::obool_from_dafny(dafny_value.Truncated().clone()))
          .build()


}
