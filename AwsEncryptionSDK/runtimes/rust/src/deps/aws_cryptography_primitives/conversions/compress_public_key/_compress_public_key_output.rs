// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::deps::aws_cryptography_primitives::operation::compress_public_key::CompressPublicKeyOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::primitives::internaldafny::types::CompressPublicKeyOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::primitives::internaldafny::types::CompressPublicKeyOutput::CompressPublicKeyOutput {
        compressedPublicKey: crate::standard_library_conversions::blob_to_dafny(&value.compressed_public_key.unwrap()),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::primitives::internaldafny::types::CompressPublicKeyOutput,
    >,
) -> crate::deps::aws_cryptography_primitives::operation::compress_public_key::CompressPublicKeyOutput {
    crate::deps::aws_cryptography_primitives::operation::compress_public_key::CompressPublicKeyOutput::builder()
        .set_compressed_public_key(Some(crate::standard_library_conversions::blob_from_dafny(dafny_value.compressedPublicKey().clone())))
        .build()
        .unwrap()
}
