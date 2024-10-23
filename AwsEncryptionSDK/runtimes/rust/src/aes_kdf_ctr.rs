// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]

#[allow(non_snake_case)]
pub mod AesKdfCtr {
    use crate::software::amazon::cryptography::primitives::internaldafny::types::Error as DafnyError;
    use crate::*;
    use aws_lc_rs::cipher::{EncryptingKey, EncryptionContext, UnboundCipherKey, AES_256};
    use dafny_runtime::Sequence;
    use std::rc::Rc;

    #[allow(non_camel_case_types)]
    // pub struct _default {}

    fn error(s: &str) -> Rc<DafnyError> {
        Rc::new(DafnyError::AwsCryptographicPrimitivesError {
            message:
                dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(s),
        })
    }

    fn as_array(nonce: &[u8]) -> &[u8; aws_lc_rs::iv::IV_LEN_128_BIT] {
        nonce.try_into().unwrap()
    }

    fn ctr_stream(nonce: &[u8], key: &[u8], length: u32) -> Result<Vec<u8>, String> {
        if nonce.len() != aws_lc_rs::iv::IV_LEN_128_BIT {
            return Err(format!(
                "Nonce length of {} not supported in AesKdfCtrStream. Nonce length must be {}.",
                nonce.len(),
                aws_lc_rs::iv::IV_LEN_128_BIT
            ));
        }

        let mut in_out_buffer = vec![0; length as usize];

        let key = UnboundCipherKey::new(&AES_256, key).map_err(|e| format!("new {:?}", e))?;
        let encrypting_key = EncryptingKey::ctr(key).map_err(|e| format!("new {:?}", e))?;
        let nonce = aws_lc_rs::iv::FixedLength::<16>::from(as_array(nonce));
        let context = EncryptionContext::Iv128(nonce);
        encrypting_key
            .less_safe_encrypt(&mut in_out_buffer, context)
            .map_err(|e| format!("new {:?}", e))?;
        Ok(in_out_buffer)
    }

    impl crate::AesKdfCtr::_default {
        #[allow(non_snake_case)]
        pub fn AesKdfCtrStream(
            nonce: &Sequence<u8>,
            key: &Sequence<u8>,
            length: u32,
        ) -> Rc<
            _Wrappers_Compile::Result<
                Sequence<u8>,
                Rc<crate::software::amazon::cryptography::primitives::internaldafny::types::Error>,
            >,
        > {
            let nonce: Vec<u8> = nonce.iter().collect();
            let key: Vec<u8> = key.iter().collect();
            match ctr_stream(&nonce, &key, length) {
                Ok(x) => Rc::new(_Wrappers_Compile::Result::Success {
                    value: x.iter().cloned().collect(),
                }),
                Err(e) => {
                    let msg = format!("Aes Kdf Ctr : {}", e);
                    Rc::new(_Wrappers_Compile::Result::Failure { error: error(&msg) })
                }
            }
        }
    }
}
