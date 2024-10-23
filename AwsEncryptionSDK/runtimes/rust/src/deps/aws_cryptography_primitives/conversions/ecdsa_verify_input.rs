// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput,
) -> crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput {
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput::ECDSAVerifyInput {
        signatureAlgorithm: crate::deps::aws_cryptography_primitives::conversions::ecdsa_signature_algorithm::to_dafny(value.signature_algorithm.clone().unwrap()),
 verificationKey: crate::standard_library_conversions::blob_to_dafny(&value.verification_key.unwrap()),
 message: crate::standard_library_conversions::blob_to_dafny(&value.message.unwrap()),
 signature: crate::standard_library_conversions::blob_to_dafny(&value.signature.unwrap()),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput,
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
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput,
    >,
) -> crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput,
) -> crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput {
    match dafny_value {
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput::ECDSAVerifyInput {..} =>
            crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput::builder()
                .set_signature_algorithm(Some( crate::deps::aws_cryptography_primitives::conversions::ecdsa_signature_algorithm::from_dafny(dafny_value.signatureAlgorithm()) ))
 .set_verification_key(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.verificationKey().clone())))
 .set_message(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.message().clone())))
 .set_signature(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.signature().clone())))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::ECDSAVerifyInput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_primitives::types::EcdsaVerifyInput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
