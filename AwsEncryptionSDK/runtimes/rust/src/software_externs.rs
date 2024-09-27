// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]
#![allow(non_snake_case)]

pub mod software {
    pub mod amazon {
        pub mod cryptography {
            pub mod internaldafny {
                pub mod StormTrackingCMC {
                    pub use crate::storm_tracker::internal_StormTrackingCMC::*;
                }
                pub mod SynchronizedLocalCMC {
                    pub use crate::local_cmc::internal_SynchronizedLocalCMC::*;
                }
            }
            pub mod dbencryptionsdk {
                pub mod dynamodb {
                    pub mod itemencryptor {
                        pub mod internaldafny {
                            pub mod legacy {
                                use crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::Error as DafnyError;
                                use crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::internaldafny::types::LegacyPolicy;
                                use ::std::rc::Rc;
                                type Legacy = ::dafny_runtime::Object<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::legacy::InternalLegacyOverride>;

                                fn error(s: &str) -> Rc<DafnyError> {
                                    Rc::new(DafnyError::DynamoDbItemEncryptorException {
                                        message:
                                            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(s),
                                    })
                                }
                                pub struct InternalLegacyOverride {
                                    pub r#__i_policy: Rc<LegacyPolicy>,
                                }
                                fn fail_override() -> Rc<
                                    crate::_Wrappers_Compile::Result<
                                        Rc<crate::_Wrappers_Compile::Option<Legacy>>,
                                        Rc<DafnyError>,
                                    >,
                                > {
                                    Rc::new(crate::_Wrappers_Compile::Result::Failure {
                                        error: error("Legacy configuration unsupported."),
                                    })
                                }
                                fn success_override() -> Rc<
                                    crate::_Wrappers_Compile::Result<
                                        Rc<crate::_Wrappers_Compile::Option<Legacy>>,
                                        Rc<DafnyError>,
                                    >,
                                > {
                                    Rc::new(crate::_Wrappers_Compile::Result::Success {
                                        value: Rc::new(crate::_Wrappers_Compile::Option::None {}),
                                    })
                                }

                                impl InternalLegacyOverride {
                                    pub fn Build(
                                        config: &Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::DynamoDbItemEncryptorConfig>,
                                    ) -> Rc<
                                        crate::_Wrappers_Compile::Result<
                                            Rc<crate::_Wrappers_Compile::Option<Legacy>>,
                                            Rc<DafnyError>,
                                        >,
                                    > {
                                        match &**config.legacyOverride() {
                                            crate::_Wrappers_Compile::Option::Some{value} => {
                                                match &**value.policy() {
                                                    LegacyPolicy::FORBID_LEGACY_ENCRYPT_FORBID_LEGACY_DECRYPT{} => success_override(),
                                                    _ => fail_override()
                                                }
                                            }
                                            crate::_Wrappers_Compile::Option::None{} => success_override()
                                        }
                                    }
                                    pub fn EncryptItem(&mut self, _input: &Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::EncryptItemInput>) -> Rc<crate::_Wrappers_Compile::Result<Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::EncryptItemOutput>, Rc<DafnyError>>>{
                                        todo!("InternalLLegacyOverride::EncryptItem")
                                    }
                                    pub fn DecryptItem(&mut self, _input: &Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::DecryptItemInput>) -> Rc<crate::_Wrappers_Compile::Result<Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::DecryptItemOutput>, Rc<DafnyError>>>{
                                        todo!("InternalLLegacyOverride::DecryptItem")
                                    }
                                    pub fn IsLegacyInput(
                                        &self,
                                        _input: &Rc<crate::software::amazon::cryptography::dbencryptionsdk::dynamodb::itemencryptor::internaldafny::types::DecryptItemInput>,
                                    ) -> bool {
                                        false
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
