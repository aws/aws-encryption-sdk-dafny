// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::types::EncryptOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::EncryptOutput,
) -> crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput {
    crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput::EncryptOutput {
        ciphertext: crate::standard_library_conversions::blob_to_dafny(&value.ciphertext.unwrap()),
 encryptionContext: ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&value.encryption_context.clone().unwrap(),
    |k| dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&k.as_bytes().to_vec(), |b| *b),
    |v| dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&v.as_bytes().to_vec(), |b| *b),
)
,
 algorithmSuiteId: crate::deps::aws_cryptography_materialProviders::conversions::esdk_algorithm_suite_id::to_dafny(value.algorithm_suite_id.clone().unwrap()),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::types::EncryptOutput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput,
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
        crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput,
    >,
) -> crate::types::EncryptOutput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput,
) -> crate::types::EncryptOutput {
    match dafny_value {
        crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput::EncryptOutput {..} =>
            crate::types::EncryptOutput::builder()
                .set_ciphertext(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.ciphertext().clone())))
 .set_encryption_context(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(&dafny_value.encryptionContext(),
    |k: &::dafny_runtime::dafny_runtime_conversions::DafnySequence<u8>| ::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&::std::borrow::Borrow::borrow(k), |b| *b)).unwrap(),
    |v: &::dafny_runtime::dafny_runtime_conversions::DafnySequence<u8>| ::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&::std::borrow::Borrow::borrow(v), |b| *b)).unwrap(),
)
 ))
 .set_algorithm_suite_id(Some( crate::deps::aws_cryptography_materialProviders::conversions::esdk_algorithm_suite_id::from_dafny(dafny_value.algorithmSuiteId()) ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::encryptionsdk::internaldafny::types::EncryptOutput,
    >>>,
) -> ::std::option::Option<crate::types::EncryptOutput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}