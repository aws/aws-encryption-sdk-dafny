// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput,
) -> crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput {
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput::OnDecryptInput {
        materials: crate::deps::aws_cryptography_materialProviders::conversions::decryption_materials::to_dafny(&value.materials.clone().unwrap())
,
 encryptedDataKeys: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&value.encrypted_data_keys.clone().unwrap(),
    |e| crate::deps::aws_cryptography_materialProviders::conversions::encrypted_data_key::to_dafny(&e.clone())
,
)
,
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput,
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
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput,
    >,
) -> crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput,
) -> crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput {
    match dafny_value {
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput::OnDecryptInput {..} =>
            crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput::builder()
                .set_materials(Some( crate::deps::aws_cryptography_materialProviders::conversions::decryption_materials::from_dafny(dafny_value.materials().clone())
 ))
 .set_encrypted_data_keys(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(dafny_value.encryptedDataKeys(),
    |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::EncryptedDataKey>| crate::deps::aws_cryptography_materialProviders::conversions::encrypted_data_key::from_dafny(e.clone())
,
)
 ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnDecryptInput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::OnDecryptInput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
