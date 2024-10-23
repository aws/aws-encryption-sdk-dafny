// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_primitives::types::RsaDecryptInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_primitives::types::RsaDecryptInput,
) -> crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput {
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput::RSADecryptInput {
        padding: crate::deps::aws_cryptography_primitives::conversions::rsa_padding_mode::to_dafny(value.padding.clone().unwrap()),
 privateKey: crate::standard_library_conversions::blob_to_dafny(&value.private_key.unwrap()),
 cipherText: crate::standard_library_conversions::blob_to_dafny(&value.cipher_text.unwrap()),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::RsaDecryptInput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput,
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
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput,
    >,
) -> crate::deps::aws_cryptography_primitives::types::RsaDecryptInput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput,
) -> crate::deps::aws_cryptography_primitives::types::RsaDecryptInput {
    match dafny_value {
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput::RSADecryptInput {..} =>
            crate::deps::aws_cryptography_primitives::types::RsaDecryptInput::builder()
                .set_padding(Some( crate::deps::aws_cryptography_primitives::conversions::rsa_padding_mode::from_dafny(dafny_value.padding()) ))
 .set_private_key(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.privateKey().clone())))
 .set_cipher_text(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.cipherText().clone())))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::RSADecryptInput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_primitives::types::RsaDecryptInput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
