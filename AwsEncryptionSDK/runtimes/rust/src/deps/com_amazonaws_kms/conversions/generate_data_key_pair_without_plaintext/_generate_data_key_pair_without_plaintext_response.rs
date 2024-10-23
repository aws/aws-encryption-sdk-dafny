// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::generate_data_key_pair_without_plaintext::GenerateDataKeyPairWithoutPlaintextOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairWithoutPlaintextResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairWithoutPlaintextResponse::GenerateDataKeyPairWithoutPlaintextResponse {
        PrivateKeyCiphertextBlob: crate::standard_library_conversions::oblob_to_dafny(&value.private_key_ciphertext_blob),
 PublicKey: crate::standard_library_conversions::oblob_to_dafny(&value.public_key),
 KeyId: crate::standard_library_conversions::ostring_to_dafny(&value.key_id),
 KeyPairSpec: ::std::rc::Rc::new(match &value.key_pair_spec {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::deps::com_amazonaws_kms::conversions::data_key_pair_spec::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairWithoutPlaintextResponse,
    >
) -> aws_sdk_kms::operation::generate_data_key_pair_without_plaintext::GenerateDataKeyPairWithoutPlaintextOutput {
    aws_sdk_kms::operation::generate_data_key_pair_without_plaintext::GenerateDataKeyPairWithoutPlaintextOutput::builder()
          .set_private_key_ciphertext_blob(crate::standard_library_conversions::oblob_from_dafny(dafny_value.PrivateKeyCiphertextBlob().clone()))
 .set_public_key(crate::standard_library_conversions::oblob_from_dafny(dafny_value.PublicKey().clone()))
 .set_key_id(crate::standard_library_conversions::ostring_from_dafny(dafny_value.KeyId().clone()))
 .set_key_pair_spec(match &**dafny_value.KeyPairSpec() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::deps::com_amazonaws_kms::conversions::data_key_pair_spec::from_dafny(value)
    ),
    _ => None,
}
)
          .build()


}
