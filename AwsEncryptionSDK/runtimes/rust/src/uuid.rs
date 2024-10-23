// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]

use crate::*;
use ::uuid::Uuid;

impl crate::UUID::_default {
    #[allow(non_snake_case)]
    pub fn ToByteArray(
        bytes: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
    ) -> ::std::rc::Rc<
        _Wrappers_Compile::Result<
            ::dafny_runtime::Sequence<u8>,
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        >,
    > {
        let my_str =
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(
                bytes,
            );
        match Uuid::parse_str(&my_str) {
                Ok(u) => {
                    let b = u.as_bytes();
                    std::rc::Rc::new(_Wrappers_Compile::Result::Success { value :
                        b.iter().cloned().collect()
                    })
                }
                Err(e) => {
                    std::rc::Rc::new(_Wrappers_Compile::Result::Failure{ error :
                        dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(
                            &format!("{my_str} is not a valid UUID ({e})."))
                    })
                }
            }
    }

    #[allow(non_snake_case)]
    pub fn FromByteArray(
        bytes: &::dafny_runtime::Sequence<u8>,
    ) -> ::std::rc::Rc<
        _Wrappers_Compile::Result<
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        >,
    > {
        let vec: Vec<u8> = bytes.iter().collect();
        if vec.len() != 16 {
            return std::rc::Rc::new(_Wrappers_Compile::Result::Failure{ error :
                    dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string("Not 16 bytes of input to FromByteArray.")
                });
        }
        let bytes: ::uuid::Bytes = vec[..16].try_into().unwrap();
        let uuid = Uuid::from_bytes_ref(&bytes);
        let my_str = uuid.to_string();
        std::rc::Rc::new(_Wrappers_Compile::Result::Success { value :
                dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&my_str)
            })
    }

    #[allow(non_snake_case)]
    pub fn GenerateUUID() -> ::std::rc::Rc<
        _Wrappers_Compile::Result<
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        >,
    > {
        let my_str = Uuid::new_v4().to_string();
        std::rc::Rc::new(_Wrappers_Compile::Result::Success { value :
                dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&my_str)
            })
    }
}
