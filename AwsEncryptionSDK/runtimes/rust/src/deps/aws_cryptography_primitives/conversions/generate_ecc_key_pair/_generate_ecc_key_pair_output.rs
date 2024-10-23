// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::deps::aws_cryptography_primitives::operation::generate_ecc_key_pair::GenerateEccKeyPairOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::GenerateECCKeyPairOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::primitives::internaldafny::types::GenerateECCKeyPairOutput::GenerateECCKeyPairOutput {
        eccCurve: crate::deps::aws_cryptography_primitives::conversions::ecdh_curve_spec::to_dafny(value.ecc_curve.clone().unwrap()),
 privateKey: crate::deps::aws_cryptography_primitives::conversions::ecc_private_key::to_dafny(&value.private_key.clone().unwrap())
,
 publicKey: crate::deps::aws_cryptography_primitives::conversions::ecc_public_key::to_dafny(&value.public_key.clone().unwrap())
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::GenerateECCKeyPairOutput,
    >,
) -> crate::deps::aws_cryptography_primitives::operation::generate_ecc_key_pair::GenerateEccKeyPairOutput {
    crate::deps::aws_cryptography_primitives::operation::generate_ecc_key_pair::GenerateEccKeyPairOutput::builder()
        .set_ecc_curve(Some( crate::deps::aws_cryptography_primitives::conversions::ecdh_curve_spec::from_dafny(dafny_value.eccCurve()) ))
 .set_private_key(Some( crate::deps::aws_cryptography_primitives::conversions::ecc_private_key::from_dafny(dafny_value.privateKey().clone())
 ))
 .set_public_key(Some( crate::deps::aws_cryptography_primitives::conversions::ecc_public_key::from_dafny(dafny_value.publicKey().clone())
 ))
        .build()
        .unwrap()
}
