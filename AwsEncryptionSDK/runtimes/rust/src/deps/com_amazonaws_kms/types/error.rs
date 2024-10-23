// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    InvalidKeyUsageException {
    error: aws_sdk_kms::types::error::InvalidKeyUsageException,
},

InvalidGrantIdException {
    error: aws_sdk_kms::types::error::InvalidGrantIdException,
},

KmsInvalidSignatureException {
    error: aws_sdk_kms::types::error::KmsInvalidSignatureException,
},

KmsInvalidStateException {
    error: aws_sdk_kms::types::error::KmsInvalidStateException,
},

ExpiredImportTokenException {
    error: aws_sdk_kms::types::error::ExpiredImportTokenException,
},

XksProxyUriUnreachableException {
    error: aws_sdk_kms::types::error::XksProxyUriUnreachableException,
},

XksKeyNotFoundException {
    error: aws_sdk_kms::types::error::XksKeyNotFoundException,
},

CustomKeyStoreHasCmKsException {
    error: aws_sdk_kms::types::error::CustomKeyStoreHasCmKsException,
},

XksProxyVpcEndpointServiceNotFoundException {
    error: aws_sdk_kms::types::error::XksProxyVpcEndpointServiceNotFoundException,
},

MalformedPolicyDocumentException {
    error: aws_sdk_kms::types::error::MalformedPolicyDocumentException,
},

ConflictException {
    error: aws_sdk_kms::types::error::ConflictException,
},

KeyUnavailableException {
    error: aws_sdk_kms::types::error::KeyUnavailableException,
},

XksKeyInvalidConfigurationException {
    error: aws_sdk_kms::types::error::XksKeyInvalidConfigurationException,
},

KmsInternalException {
    error: aws_sdk_kms::types::error::KmsInternalException,
},

InvalidMarkerException {
    error: aws_sdk_kms::types::error::InvalidMarkerException,
},

KmsInvalidMacException {
    error: aws_sdk_kms::types::error::KmsInvalidMacException,
},

InvalidGrantTokenException {
    error: aws_sdk_kms::types::error::InvalidGrantTokenException,
},

AlreadyExistsException {
    error: aws_sdk_kms::types::error::AlreadyExistsException,
},

UnsupportedOperationException {
    error: aws_sdk_kms::types::error::UnsupportedOperationException,
},

InvalidAliasNameException {
    error: aws_sdk_kms::types::error::InvalidAliasNameException,
},

XksProxyVpcEndpointServiceInUseException {
    error: aws_sdk_kms::types::error::XksProxyVpcEndpointServiceInUseException,
},

DryRunOperationException {
    error: aws_sdk_kms::types::error::DryRunOperationException,
},

DependencyTimeoutException {
    error: aws_sdk_kms::types::error::DependencyTimeoutException,
},

XksProxyUriEndpointInUseException {
    error: aws_sdk_kms::types::error::XksProxyUriEndpointInUseException,
},

CustomKeyStoreInvalidStateException {
    error: aws_sdk_kms::types::error::CustomKeyStoreInvalidStateException,
},

InvalidArnException {
    error: aws_sdk_kms::types::error::InvalidArnException,
},

XksProxyIncorrectAuthenticationCredentialException {
    error: aws_sdk_kms::types::error::XksProxyIncorrectAuthenticationCredentialException,
},

CustomKeyStoreNotFoundException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNotFoundException,
},

XksProxyInvalidConfigurationException {
    error: aws_sdk_kms::types::error::XksProxyInvalidConfigurationException,
},

IncorrectKeyMaterialException {
    error: aws_sdk_kms::types::error::IncorrectKeyMaterialException,
},

IncorrectTrustAnchorException {
    error: aws_sdk_kms::types::error::IncorrectTrustAnchorException,
},

InvalidCiphertextException {
    error: aws_sdk_kms::types::error::InvalidCiphertextException,
},

DisabledException {
    error: aws_sdk_kms::types::error::DisabledException,
},

CloudHsmClusterNotFoundException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotFoundException,
},

TagException {
    error: aws_sdk_kms::types::error::TagException,
},

XksProxyVpcEndpointServiceInvalidConfigurationException {
    error: aws_sdk_kms::types::error::XksProxyVpcEndpointServiceInvalidConfigurationException,
},

CloudHsmClusterNotActiveException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotActiveException,
},

CloudHsmClusterInUseException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInUseException,
},

LimitExceededException {
    error: aws_sdk_kms::types::error::LimitExceededException,
},

XksProxyUriInUseException {
    error: aws_sdk_kms::types::error::XksProxyUriInUseException,
},

CustomKeyStoreNameInUseException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNameInUseException,
},

InvalidImportTokenException {
    error: aws_sdk_kms::types::error::InvalidImportTokenException,
},

CloudHsmClusterNotRelatedException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotRelatedException,
},

XksProxyInvalidResponseException {
    error: aws_sdk_kms::types::error::XksProxyInvalidResponseException,
},

IncorrectKeyException {
    error: aws_sdk_kms::types::error::IncorrectKeyException,
},

XksKeyAlreadyInUseException {
    error: aws_sdk_kms::types::error::XksKeyAlreadyInUseException,
},

NotFoundException {
    error: aws_sdk_kms::types::error::NotFoundException,
},

CloudHsmClusterInvalidConfigurationException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInvalidConfigurationException,
},
    Opaque {
        obj: ::dafny_runtime::Object<dyn ::std::any::Any>,
	alt_text : String
    },
}

impl ::std::cmp::Eq for Error {}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ::std::error::Error for Error {}
