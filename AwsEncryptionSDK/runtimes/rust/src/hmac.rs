// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]

use crate::software::amazon::cryptography::primitives::internaldafny::types::DigestAlgorithm;
use crate::*;
use aws_lc_rs::hmac;

fn convert_algorithm(input: &DigestAlgorithm) -> hmac::Algorithm {
    match input {
        DigestAlgorithm::SHA_512 {} => hmac::HMAC_SHA512,
        DigestAlgorithm::SHA_384 {} => hmac::HMAC_SHA384,
        DigestAlgorithm::SHA_256 {} => hmac::HMAC_SHA256,
    }
}

// Let's implement HMAC::_default::Digest
impl crate::HMAC::_default {
    #[allow(non_snake_case)]
    pub fn Digest(
        input: &::std::rc::Rc<
            crate::software::amazon::cryptography::primitives::internaldafny::types::HMacInput,
        >,
    ) -> ::std::rc::Rc<
        _Wrappers_Compile::Result<
            ::dafny_runtime::Sequence<u8>,
            ::std::rc::Rc<software::amazon::cryptography::primitives::internaldafny::types::Error>,
        >,
    > {
        let key_vec: Vec<u8> = input.key().iter().collect();
        let the_key = hmac::Key::new(convert_algorithm(input.digestAlgorithm()), &key_vec);
        let message_vec: Vec<u8> = input.message().iter().collect();
        let result = hmac::sign(&the_key, &message_vec);
        ::std::rc::Rc::new(_Wrappers_Compile::Result::Success {
            value: result.as_ref().iter().cloned().collect(),
        })
    }
}

#[allow(non_snake_case)]
pub mod HMAC {
    use crate::*;
    use aws_lc_rs::hmac;
    #[allow(non_camel_case_types)]
    pub struct _default {}

    #[derive(Debug)]
    pub struct HMac {
        algorithm: hmac::Algorithm,
        context: Option<hmac::Context>,
        key: Option<hmac::Key>,
    }
    impl HMac {
        pub fn Init(&mut self, salt: &::dafny_runtime::Sequence<u8>) {
            let salt: Vec<u8> = salt.iter().collect();
            self.key = Some(hmac::Key::new(self.algorithm, &salt));
            self.context = Some(hmac::Context::with_key(self.key.as_ref().unwrap()));
        }
        pub fn re_init(&mut self) {
            self.context = Some(hmac::Context::with_key(self.key.as_ref().unwrap()));
        }
        pub fn Build(
            input: &::std::rc::Rc<
                software::amazon::cryptography::primitives::internaldafny::types::DigestAlgorithm,
            >,
        ) -> ::std::rc::Rc<
            _Wrappers_Compile::Result<
                ::dafny_runtime::Object<Self>,
                ::std::rc::Rc<
                    software::amazon::cryptography::primitives::internaldafny::types::Error,
                >,
            >,
        > {
            let inner = dafny_runtime::Object::new(Self {
                algorithm: super::convert_algorithm(input),
                context: None,
                key: None,
            });

            ::std::rc::Rc::new(_Wrappers_Compile::Result::Success { value: inner })
        }
        pub fn BlockUpdate(&mut self, block: &::dafny_runtime::Sequence<u8>) {
            let part: Vec<u8> = block.iter().collect();
            self.context.as_mut().unwrap().update(&part);
        }
        pub fn GetResult(&mut self) -> ::dafny_runtime::Sequence<u8> {
            let inner = self.context.take();
            match inner {
                Some(x) => {
                    let tag = x.sign();
                    // other languages allow you to call BlockUpdate after GetResult
                    // so we re-initialize to mimic that behavior
                    self.re_init();
                    tag.as_ref().iter().cloned().collect()
                }
                None => [].iter().cloned().collect(),
            }
        }
    }
}
