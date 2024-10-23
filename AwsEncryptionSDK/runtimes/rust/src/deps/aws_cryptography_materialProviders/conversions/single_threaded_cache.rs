// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache,
) -> crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache {
    crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache::SingleThreadedCache {
        entryCapacity: value.entry_capacity.clone().unwrap(),
 entryPruningTailSize: crate::standard_library_conversions::oint_to_dafny(value.entry_pruning_tail_size),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache,
>>>{
    ::std::rc::Rc::new(match value {
        ::std::option::Option::None => crate::_Wrappers_Compile::Option::None {},
        ::std::option::Option::Some(x) => crate::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(to_dafny_plain(x)),
        },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache,
    >,
) -> crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache,
) -> crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache {
    match dafny_value {
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache::SingleThreadedCache {..} =>
            crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache::builder()
                .set_entry_capacity(Some( dafny_value.entryCapacity() .clone() ))
 .set_entry_pruning_tail_size(crate::standard_library_conversions::oint_from_dafny(dafny_value.entryPruningTailSize().clone()))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#software::amazon::cryptography::materialproviders::internaldafny::types::SingleThreadedCache,
    >>>,
) -> ::std::option::Option<crate::deps::aws_cryptography_materialProviders::types::SingleThreadedCache> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
