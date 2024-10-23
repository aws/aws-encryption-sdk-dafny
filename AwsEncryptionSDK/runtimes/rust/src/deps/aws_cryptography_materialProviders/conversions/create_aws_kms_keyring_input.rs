// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput,
) -> crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput {
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput::CreateAwsKmsKeyringInput {
        kmsKeyId: crate::standard_library_conversions::ostring_to_dafny(&value.kms_key_id) .Extract(),
 kmsClient: crate::deps::com_amazonaws_kms::conversions::client::to_dafny(&value.kms_client.clone().unwrap())
,
 grantTokens: ::std::rc::Rc::new(match &value.grant_tokens {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&e),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput,
>>>{
    ::std::rc::Rc::new(match value {
        ::std::option::Option::None => crate::_Wrappers_Compile::Option::None {},
        ::std::option::Option::Some(x) => crate::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(to_dafny_plain(x)),
        },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput,
    >,
) -> crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput,
) -> crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput {
    match dafny_value {
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput::CreateAwsKmsKeyringInput {..} =>
            crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput::builder()
                .set_kms_key_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.kmsKeyId()) ))
 .set_kms_client(Some( crate::deps::com_amazonaws_kms::conversions::client::from_dafny(dafny_value.kmsClient().clone())
 ))
 .set_grant_tokens(match (*dafny_value.grantTokens()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::dafny_runtime::dafny_runtime_conversions::DafnySequence<::dafny_runtime::dafny_runtime_conversions::DafnyCharUTF16>| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::CreateAwsKmsKeyringInput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::CreateAwsKmsKeyringInput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
