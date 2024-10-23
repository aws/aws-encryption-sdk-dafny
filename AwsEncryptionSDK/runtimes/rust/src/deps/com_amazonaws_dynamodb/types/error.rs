// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    LimitExceededException {
    error: aws_sdk_dynamodb::types::error::LimitExceededException,
},

ConditionalCheckFailedException {
    error: aws_sdk_dynamodb::types::error::ConditionalCheckFailedException,
},

IdempotentParameterMismatchException {
    error: aws_sdk_dynamodb::types::error::IdempotentParameterMismatchException,
},

TableAlreadyExistsException {
    error: aws_sdk_dynamodb::types::error::TableAlreadyExistsException,
},

TableInUseException {
    error: aws_sdk_dynamodb::types::error::TableInUseException,
},

ReplicaAlreadyExistsException {
    error: aws_sdk_dynamodb::types::error::ReplicaAlreadyExistsException,
},

ResourceInUseException {
    error: aws_sdk_dynamodb::types::error::ResourceInUseException,
},

ImportConflictException {
    error: aws_sdk_dynamodb::types::error::ImportConflictException,
},

InvalidExportTimeException {
    error: aws_sdk_dynamodb::types::error::InvalidExportTimeException,
},

PointInTimeRecoveryUnavailableException {
    error: aws_sdk_dynamodb::types::error::PointInTimeRecoveryUnavailableException,
},

IndexNotFoundException {
    error: aws_sdk_dynamodb::types::error::IndexNotFoundException,
},

ResourceNotFoundException {
    error: aws_sdk_dynamodb::types::error::ResourceNotFoundException,
},

ExportConflictException {
    error: aws_sdk_dynamodb::types::error::ExportConflictException,
},

GlobalTableNotFoundException {
    error: aws_sdk_dynamodb::types::error::GlobalTableNotFoundException,
},

TransactionCanceledException {
    error: aws_sdk_dynamodb::types::error::TransactionCanceledException,
},

TableNotFoundException {
    error: aws_sdk_dynamodb::types::error::TableNotFoundException,
},

ReplicaNotFoundException {
    error: aws_sdk_dynamodb::types::error::ReplicaNotFoundException,
},

TransactionInProgressException {
    error: aws_sdk_dynamodb::types::error::TransactionInProgressException,
},

BackupNotFoundException {
    error: aws_sdk_dynamodb::types::error::BackupNotFoundException,
},

BackupInUseException {
    error: aws_sdk_dynamodb::types::error::BackupInUseException,
},

TransactionConflictException {
    error: aws_sdk_dynamodb::types::error::TransactionConflictException,
},

ContinuousBackupsUnavailableException {
    error: aws_sdk_dynamodb::types::error::ContinuousBackupsUnavailableException,
},

ItemCollectionSizeLimitExceededException {
    error: aws_sdk_dynamodb::types::error::ItemCollectionSizeLimitExceededException,
},

ProvisionedThroughputExceededException {
    error: aws_sdk_dynamodb::types::error::ProvisionedThroughputExceededException,
},

InternalServerError {
    error: aws_sdk_dynamodb::types::error::InternalServerError,
},

RequestLimitExceeded {
    error: aws_sdk_dynamodb::types::error::RequestLimitExceeded,
},

ExportNotFoundException {
    error: aws_sdk_dynamodb::types::error::ExportNotFoundException,
},

DuplicateItemException {
    error: aws_sdk_dynamodb::types::error::DuplicateItemException,
},

ImportNotFoundException {
    error: aws_sdk_dynamodb::types::error::ImportNotFoundException,
},

GlobalTableAlreadyExistsException {
    error: aws_sdk_dynamodb::types::error::GlobalTableAlreadyExistsException,
},

InvalidEndpointException {
    error: aws_sdk_dynamodb::types::error::InvalidEndpointException,
},

InvalidRestoreTimeException {
    error: aws_sdk_dynamodb::types::error::InvalidRestoreTimeException,
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
