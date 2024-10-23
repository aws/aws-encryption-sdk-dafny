// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    #[allow(missing_docs)]
KeyStoreException {
    message: ::std::string::String,
},

DynamoDB_20120810Error {
    error: crate::deps::com_amazonaws_dynamodb::types::error::Error,
},

TrentServiceError {
    error: crate::deps::com_amazonaws_kms::types::error::Error,
},
    CollectionOfErrors {
        list: ::std::vec::Vec<Self>,
        message: ::std::string::String,
    },
    ValidationError(ValidationError),
    Opaque {
        obj: ::dafny_runtime::Object<dyn ::std::any::Any>,
	alt_text : ::std::string::String
    },
}

impl ::std::cmp::Eq for Error {}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            Self::ValidationError(err) => ::std::fmt::Display::fmt(err, f),
            Self::Opaque{obj, alt_text} => ::std::fmt::Debug::fmt(alt_text, f),
            _ => ::std::fmt::Debug::fmt(self, f),
        }
    }
}

impl ::std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ValidationError(err) => Some(err),
            _ => None,
        }
    }
}

impl Error {
    pub fn wrap_validation_err<E>(err: E) -> Self
    where
        E: ::std::error::Error + 'static,
    {
        Self::ValidationError(ValidationError(::std::rc::Rc::new(err)))
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub(crate) struct ValidationError(::std::rc::Rc<dyn ::std::error::Error>);

impl ::std::cmp::PartialEq for ValidationError {
    fn eq(&self, other: &Self) -> bool {
        ::std::rc::Rc::<(dyn std::error::Error + 'static)>::ptr_eq(&self.0, &other.0)
    }
}

impl ::std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        ::std::fmt::Display::fmt(&self.0, f)
    }
}

impl ::std::error::Error for ValidationError {
    fn source(&self) -> ::std::option::Option<&(dyn ::std::error::Error + 'static)> {
        ::std::option::Option::Some(self.0.as_ref())
    }
}
