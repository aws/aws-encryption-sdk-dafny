// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]

#[allow(non_snake_case)]
pub mod DafnyLibraries {
    use dashmap::DashMap;
    use std::collections::HashMap;
    use std::collections::HashSet;

    pub struct MutableMap<K: ::dafny_runtime::DafnyTypeEq, V: ::dafny_runtime::DafnyTypeEq> {
        map: DashMap<K, V>,
    }

    impl<K: ::dafny_runtime::DafnyTypeEq, V: ::dafny_runtime::DafnyTypeEq> MutableMap<K, V> {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::Object::new(MutableMap {
                map: DashMap::new(),
            })
        }
    }

    impl<K: ::dafny_runtime::DafnyTypeEq, V: ::dafny_runtime::DafnyTypeEq>
        crate::DafnyLibraries::MutableMapTrait<K, V> for MutableMap<K, V>
    {
        fn content(&self) -> ::dafny_runtime::Map<K, V> {
            let mut new_map = HashMap::new();
            for entry in self.map.iter() {
                new_map.insert(entry.key().clone(), entry.value().clone());
            }
            dafny_runtime::Map::from_hashmap_owned(new_map)
        }
        fn Put(&self, k: &K, v: &V) {
            self.map.insert(k.clone(), v.clone());
        }
        fn Keys(&self) -> ::dafny_runtime::Set<K> {
            let mut new_set = HashSet::new();
            for entry in self.map.iter() {
                new_set.insert(entry.key().clone());
            }
            dafny_runtime::Set::from_hashset_owned(new_set)
        }
        fn HasKey(&self, k: &K) -> bool {
            self.map.contains_key(k)
        }
        fn Values(&self) -> ::dafny_runtime::Set<V> {
            let mut new_set = HashSet::new();
            for entry in self.map.iter() {
                new_set.insert(entry.value().clone());
            }
            dafny_runtime::Set::from_hashset_owned(new_set)
        }
        fn Items(&self) -> ::dafny_runtime::Set<(K, V)> {
            let mut new_set = HashSet::new();
            for entry in self.map.iter() {
                new_set.insert((entry.key().clone(), entry.value().clone()));
            }
            dafny_runtime::Set::from_hashset_owned(new_set)
        }
        fn Select(&self, k: &K) -> V {
            self.map.get(k).unwrap().clone()
        }
        fn Remove(&self, k: &K) {
            self.map.remove(k);
        }
        fn Size(&self) -> ::dafny_runtime::DafnyInt {
            self.map.len().into()
        }
    }

    pub mod FileIO {
        use std::fs::File;
        use std::io::Read;
        use std::io::Write;
        use std::path::Path;

        pub fn INTERNAL_ReadBytesFromFile(
            file: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> (
            bool,
            ::dafny_runtime::Sequence<u8>,
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) {
            let file_name = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(file);
            let path = Path::new(&file_name);

            let mut file = match File::open(path) {
                Err(why) => {
                    let err_msg = format!("couldn't open {} for reading: {}", path.display(), why);
                    let err_msg = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&err_msg);
                    return (true, dafny_runtime::Sequence::default(), err_msg);
                }
                Ok(file) => file,
            };

            let mut result = Vec::new();
            match file.read_to_end(&mut result) {
                Err(why) => {
                    let err_msg = format!("couldn't read from {}: {}", path.display(), why);
                    let err_msg = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&err_msg);
                    (true, dafny_runtime::Sequence::default(), err_msg)
                }
                Ok(_) => (
                    false,
                    dafny_runtime::Sequence::from_array_owned(result),
                    dafny_runtime::Sequence::default(),
                ),
            }
        }

        pub fn INTERNAL_WriteBytesToFile(
            path: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            bytes: &::dafny_runtime::Sequence<u8>,
        ) -> (
            bool,
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) {
            let file_name = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(path);
            let path = Path::new(&file_name);

            let maybe_file = std::fs::OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(path);
            let mut file = match maybe_file {
                Err(why) => {
                    let err_msg = format!("couldn't open {} for writing: {}", path.display(), why);
                    let err_msg = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&err_msg);
                    return (true, err_msg);
                }
                Ok(file) => file,
            };

            let bytes = bytes.to_array();
            match file.write_all(&bytes) {
                Err(why) => {
                    let err_msg =
                        format!("couldn't write all bytes to {}: {}", path.display(), why);
                    let err_msg = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&err_msg);
                    (true, err_msg)
                }
                Ok(_) => (false, dafny_runtime::Sequence::default()),
            }
        }
    }
}
