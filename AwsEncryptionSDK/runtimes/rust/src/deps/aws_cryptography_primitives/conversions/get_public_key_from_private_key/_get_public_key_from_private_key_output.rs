// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::deps::aws_cryptography_primitives::operation::get_public_key_from_private_key::GetPublicKeyFromPrivateKeyOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::GetPublicKeyFromPrivateKeyOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::primitives::internaldafny::types::GetPublicKeyFromPrivateKeyOutput::GetPublicKeyFromPrivateKeyOutput {
        eccCurve: crate::deps::aws_cryptography_primitives::conversions::ecdh_curve_spec::to_dafny(value.ecc_curve.clone().unwrap()),
 privateKey: crate::deps::aws_cryptography_primitives::conversions::ecc_private_key::to_dafny(&value.private_key.clone().unwrap())
,
 publicKey: crate::standard_library_conversions::blob_to_dafny(&value.public_key.unwrap()),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::GetPublicKeyFromPrivateKeyOutput,
    >,
) -> crate::deps::aws_cryptography_primitives::operation::get_public_key_from_private_key::GetPublicKeyFromPrivateKeyOutput {
    crate::deps::aws_cryptography_primitives::operation::get_public_key_from_private_key::GetPublicKeyFromPrivateKeyOutput::builder()
        .set_ecc_curve(Some( crate::deps::aws_cryptography_primitives::conversions::ecdh_curve_spec::from_dafny(dafny_value.eccCurve()) ))
 .set_private_key(Some( crate::deps::aws_cryptography_primitives::conversions::ecc_private_key::from_dafny(dafny_value.privateKey().clone())
 ))
 .set_public_key(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.publicKey().clone())))
        .build()
        .unwrap()
}
