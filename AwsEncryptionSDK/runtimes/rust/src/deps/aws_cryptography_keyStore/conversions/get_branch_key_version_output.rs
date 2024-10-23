// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput,
) -> crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput {
    crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput::GetBranchKeyVersionOutput {
        branchKeyMaterials: crate::deps::aws_cryptography_keyStore::conversions::branch_key_materials::to_dafny(&value.branch_key_materials.clone().unwrap())
,
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput,
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
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput,
    >,
) -> crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput,
) -> crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput {
    match dafny_value {
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput::GetBranchKeyVersionOutput {..} =>
            crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput::builder()
                .set_branch_key_materials(Some( crate::deps::aws_cryptography_keyStore::conversions::branch_key_materials::from_dafny(dafny_value.branchKeyMaterials().clone())
 ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::keystore::internaldafny::types::GetBranchKeyVersionOutput,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_keyStore::types::GetBranchKeyVersionOutput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
