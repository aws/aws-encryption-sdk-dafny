// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::deps::aws_cryptography_materialProviders::operation::on_encrypt::OnEncryptOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnEncryptOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnEncryptOutput::OnEncryptOutput {
        materials: crate::deps::aws_cryptography_materialProviders::conversions::encryption_materials::to_dafny(&value.materials.clone().unwrap())
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::OnEncryptOutput,
    >,
) -> crate::deps::aws_cryptography_materialProviders::operation::on_encrypt::OnEncryptOutput {
    crate::deps::aws_cryptography_materialProviders::operation::on_encrypt::OnEncryptOutput::builder()
        .set_materials(Some( crate::deps::aws_cryptography_materialProviders::conversions::encryption_materials::from_dafny(dafny_value.materials().clone())
 ))
        .build()
        .unwrap()
}
