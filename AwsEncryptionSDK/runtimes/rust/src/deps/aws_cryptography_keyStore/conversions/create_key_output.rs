// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput,
) -> crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput {
    crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput::CreateKeyOutput {
        branchKeyIdentifier: crate::standard_library_conversions::ostring_to_dafny(&value.branch_key_identifier) .Extract(),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput,
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
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput,
    >,
) -> crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput,
) -> crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput {
    match dafny_value {
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput::CreateKeyOutput {..} =>
            crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput::builder()
                .set_branch_key_identifier(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.branchKeyIdentifier()) ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::CreateKeyOutput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::CreateKeyOutput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
