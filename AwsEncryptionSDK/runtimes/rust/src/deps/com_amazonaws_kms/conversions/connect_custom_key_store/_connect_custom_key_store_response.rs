// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::connect_custom_key_store::ConnectCustomKeyStoreOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectCustomKeyStoreResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectCustomKeyStoreResponse::ConnectCustomKeyStoreResponse {

    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectCustomKeyStoreResponse,
    >
) -> aws_sdk_kms::operation::connect_custom_key_store::ConnectCustomKeyStoreOutput {
    aws_sdk_kms::operation::connect_custom_key_store::ConnectCustomKeyStoreOutput::builder()

          .build()


}
