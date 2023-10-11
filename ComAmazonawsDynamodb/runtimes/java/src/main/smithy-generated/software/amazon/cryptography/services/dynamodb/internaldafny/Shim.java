// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.dynamodb.internaldafny;

import Wrappers_Compile.Result;
import dafny.Tuple0;
import java.lang.Override;
import java.lang.String;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.dynamodb.model.BackupInUseException;
import software.amazon.awssdk.services.dynamodb.model.BackupNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.BatchExecuteStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchExecuteStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.BatchGetItemRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchGetItemResponse;
import software.amazon.awssdk.services.dynamodb.model.BatchWriteItemRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchWriteItemResponse;
import software.amazon.awssdk.services.dynamodb.model.ConditionalCheckFailedException;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsUnavailableException;
import software.amazon.awssdk.services.dynamodb.model.CreateBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.CreateGlobalTableRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateGlobalTableResponse;
import software.amazon.awssdk.services.dynamodb.model.CreateTableRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DeleteBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.DeleteItemRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteItemResponse;
import software.amazon.awssdk.services.dynamodb.model.DeleteTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeContinuousBackupsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeContinuousBackupsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeContributorInsightsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeContributorInsightsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeExportRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeExportResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeGlobalTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeGlobalTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeGlobalTableSettingsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeGlobalTableSettingsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeImportRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeImportResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeLimitsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeLimitsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveResponse;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.DuplicateItemException;
import software.amazon.awssdk.services.dynamodb.model.DynamoDbException;
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionResponse;
import software.amazon.awssdk.services.dynamodb.model.ExportConflictException;
import software.amazon.awssdk.services.dynamodb.model.ExportNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.ExportTableToPointInTimeRequest;
import software.amazon.awssdk.services.dynamodb.model.ExportTableToPointInTimeResponse;
import software.amazon.awssdk.services.dynamodb.model.GetItemRequest;
import software.amazon.awssdk.services.dynamodb.model.GetItemResponse;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.IdempotentParameterMismatchException;
import software.amazon.awssdk.services.dynamodb.model.ImportConflictException;
import software.amazon.awssdk.services.dynamodb.model.ImportNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.ImportTableRequest;
import software.amazon.awssdk.services.dynamodb.model.ImportTableResponse;
import software.amazon.awssdk.services.dynamodb.model.IndexNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.InternalServerErrorException;
import software.amazon.awssdk.services.dynamodb.model.InvalidExportTimeException;
import software.amazon.awssdk.services.dynamodb.model.InvalidRestoreTimeException;
import software.amazon.awssdk.services.dynamodb.model.ItemCollectionSizeLimitExceededException;
import software.amazon.awssdk.services.dynamodb.model.LimitExceededException;
import software.amazon.awssdk.services.dynamodb.model.ListBackupsRequest;
import software.amazon.awssdk.services.dynamodb.model.ListBackupsResponse;
import software.amazon.awssdk.services.dynamodb.model.ListContributorInsightsRequest;
import software.amazon.awssdk.services.dynamodb.model.ListContributorInsightsResponse;
import software.amazon.awssdk.services.dynamodb.model.ListExportsRequest;
import software.amazon.awssdk.services.dynamodb.model.ListExportsResponse;
import software.amazon.awssdk.services.dynamodb.model.ListGlobalTablesRequest;
import software.amazon.awssdk.services.dynamodb.model.ListGlobalTablesResponse;
import software.amazon.awssdk.services.dynamodb.model.ListImportsRequest;
import software.amazon.awssdk.services.dynamodb.model.ListImportsResponse;
import software.amazon.awssdk.services.dynamodb.model.ListTablesRequest;
import software.amazon.awssdk.services.dynamodb.model.ListTablesResponse;
import software.amazon.awssdk.services.dynamodb.model.ListTagsOfResourceRequest;
import software.amazon.awssdk.services.dynamodb.model.ListTagsOfResourceResponse;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryUnavailableException;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputExceededException;
import software.amazon.awssdk.services.dynamodb.model.PutItemRequest;
import software.amazon.awssdk.services.dynamodb.model.PutItemResponse;
import software.amazon.awssdk.services.dynamodb.model.QueryRequest;
import software.amazon.awssdk.services.dynamodb.model.QueryResponse;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.ReplicaNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.RequestLimitExceededException;
import software.amazon.awssdk.services.dynamodb.model.ResourceInUseException;
import software.amazon.awssdk.services.dynamodb.model.ResourceNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableFromBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableFromBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableToPointInTimeRequest;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableToPointInTimeResponse;
import software.amazon.awssdk.services.dynamodb.model.ScanRequest;
import software.amazon.awssdk.services.dynamodb.model.ScanResponse;
import software.amazon.awssdk.services.dynamodb.model.TableAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.TableInUseException;
import software.amazon.awssdk.services.dynamodb.model.TableNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.TagResourceRequest;
import software.amazon.awssdk.services.dynamodb.model.TransactGetItemsRequest;
import software.amazon.awssdk.services.dynamodb.model.TransactGetItemsResponse;
import software.amazon.awssdk.services.dynamodb.model.TransactWriteItemsRequest;
import software.amazon.awssdk.services.dynamodb.model.TransactWriteItemsResponse;
import software.amazon.awssdk.services.dynamodb.model.TransactionCanceledException;
import software.amazon.awssdk.services.dynamodb.model.TransactionConflictException;
import software.amazon.awssdk.services.dynamodb.model.TransactionInProgressException;
import software.amazon.awssdk.services.dynamodb.model.UntagResourceRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateContinuousBackupsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateContinuousBackupsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateContributorInsightsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateContributorInsightsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableSettingsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableSettingsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateItemRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateItemResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveResponse;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchExecuteStatementInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchExecuteStatementOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchGetItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchGetItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchWriteItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchWriteItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateBackupInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateBackupOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateGlobalTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateGlobalTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteBackupInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteBackupOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeBackupInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeBackupOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeContinuousBackupsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeContinuousBackupsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeContributorInsightsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeContributorInsightsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeEndpointsRequest;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeEndpointsResponse;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeExportInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeExportOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeGlobalTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeGlobalTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeGlobalTableSettingsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeGlobalTableSettingsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeImportInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeImportOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeKinesisStreamingDestinationInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeKinesisStreamingDestinationOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeLimitsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeLimitsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTableReplicaAutoScalingInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTableReplicaAutoScalingOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTimeToLiveInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeTimeToLiveOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DisableKinesisStreamingDestinationInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.DisableKinesisStreamingDestinationOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.EnableKinesisStreamingDestinationInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.EnableKinesisStreamingDestinationOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExecuteStatementInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExecuteStatementOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExecuteTransactionInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExecuteTransactionOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportTableToPointInTimeInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportTableToPointInTimeOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.GetItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.GetItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListBackupsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListBackupsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListContributorInsightsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListContributorInsightsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListExportsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListExportsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListGlobalTablesInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListGlobalTablesOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListImportsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListImportsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListTablesInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListTablesOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListTagsOfResourceInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ListTagsOfResourceOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.PutItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.PutItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.QueryInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.QueryOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.RestoreTableFromBackupInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.RestoreTableFromBackupOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.RestoreTableToPointInTimeInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.RestoreTableToPointInTimeOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ScanInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.ScanOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.TagResourceInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactGetItemsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactGetItemsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactWriteItemsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactWriteItemsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UntagResourceInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateContinuousBackupsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateContinuousBackupsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateContributorInsightsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateContributorInsightsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateGlobalTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateGlobalTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateGlobalTableSettingsInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateGlobalTableSettingsOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateItemInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateItemOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTableInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTableOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTableReplicaAutoScalingInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTableReplicaAutoScalingOutput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTimeToLiveInput;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateTimeToLiveOutput;

public class Shim implements IDynamoDBClient {
  private final DynamoDbClient _impl;

  private final String region;

  public Shim(final DynamoDbClient impl, final String region) {
    this._impl = impl;
    this.region = region;
  }

  public DynamoDbClient impl() {
    return this._impl;
  }

  public String region() {
    return this.region;
  }

  @Override
  public Result<BatchExecuteStatementOutput, Error> BatchExecuteStatement(
      BatchExecuteStatementInput input) {
    BatchExecuteStatementRequest converted = ToNative.BatchExecuteStatementInput(input);
    try {
      BatchExecuteStatementResponse result = _impl.batchExecuteStatement(converted);
      BatchExecuteStatementOutput dafnyResponse = ToDafny.BatchExecuteStatementOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<BatchGetItemOutput, Error> BatchGetItem(BatchGetItemInput input) {
    BatchGetItemRequest converted = ToNative.BatchGetItemInput(input);
    try {
      BatchGetItemResponse result = _impl.batchGetItem(converted);
      BatchGetItemOutput dafnyResponse = ToDafny.BatchGetItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<BatchWriteItemOutput, Error> BatchWriteItem(BatchWriteItemInput input) {
    BatchWriteItemRequest converted = ToNative.BatchWriteItemInput(input);
    try {
      BatchWriteItemResponse result = _impl.batchWriteItem(converted);
      BatchWriteItemOutput dafnyResponse = ToDafny.BatchWriteItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ItemCollectionSizeLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateBackupOutput, Error> CreateBackup(CreateBackupInput input) {
    CreateBackupRequest converted = ToNative.CreateBackupInput(input);
    try {
      CreateBackupResponse result = _impl.createBackup(converted);
      CreateBackupOutput dafnyResponse = ToDafny.CreateBackupOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (BackupInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ContinuousBackupsUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateGlobalTableOutput, Error> CreateGlobalTable(CreateGlobalTableInput input) {
    CreateGlobalTableRequest converted = ToNative.CreateGlobalTableInput(input);
    try {
      CreateGlobalTableResponse result = _impl.createGlobalTable(converted);
      CreateGlobalTableOutput dafnyResponse = ToDafny.CreateGlobalTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (GlobalTableAlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<CreateTableOutput, Error> CreateTable(CreateTableInput input) {
    CreateTableRequest converted = ToNative.CreateTableInput(input);
    try {
      CreateTableResponse result = _impl.createTable(converted);
      CreateTableOutput dafnyResponse = ToDafny.CreateTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DeleteBackupOutput, Error> DeleteBackup(DeleteBackupInput input) {
    DeleteBackupRequest converted = ToNative.DeleteBackupInput(input);
    try {
      DeleteBackupResponse result = _impl.deleteBackup(converted);
      DeleteBackupOutput dafnyResponse = ToDafny.DeleteBackupOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (BackupInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (BackupNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DeleteItemOutput, Error> DeleteItem(DeleteItemInput input) {
    DeleteItemRequest converted = ToNative.DeleteItemInput(input);
    try {
      DeleteItemResponse result = _impl.deleteItem(converted);
      DeleteItemOutput dafnyResponse = ToDafny.DeleteItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ConditionalCheckFailedException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ItemCollectionSizeLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DeleteTableOutput, Error> DeleteTable(DeleteTableInput input) {
    DeleteTableRequest converted = ToNative.DeleteTableInput(input);
    try {
      DeleteTableResponse result = _impl.deleteTable(converted);
      DeleteTableOutput dafnyResponse = ToDafny.DeleteTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeBackupOutput, Error> DescribeBackup(DescribeBackupInput input) {
    DescribeBackupRequest converted = ToNative.DescribeBackupInput(input);
    try {
      DescribeBackupResponse result = _impl.describeBackup(converted);
      DescribeBackupOutput dafnyResponse = ToDafny.DescribeBackupOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (BackupNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeContinuousBackupsOutput, Error> DescribeContinuousBackups(
      DescribeContinuousBackupsInput input) {
    DescribeContinuousBackupsRequest converted = ToNative.DescribeContinuousBackupsInput(input);
    try {
      DescribeContinuousBackupsResponse result = _impl.describeContinuousBackups(converted);
      DescribeContinuousBackupsOutput dafnyResponse = ToDafny.DescribeContinuousBackupsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeContributorInsightsOutput, Error> DescribeContributorInsights(
      DescribeContributorInsightsInput input) {
    DescribeContributorInsightsRequest converted = ToNative.DescribeContributorInsightsInput(input);
    try {
      DescribeContributorInsightsResponse result = _impl.describeContributorInsights(converted);
      DescribeContributorInsightsOutput dafnyResponse = ToDafny.DescribeContributorInsightsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeEndpointsResponse, Error> DescribeEndpoints(
      DescribeEndpointsRequest input) {
    software.amazon.awssdk.services.dynamodb.model.DescribeEndpointsRequest converted = ToNative.DescribeEndpointsRequest(input);
    try {
      software.amazon.awssdk.services.dynamodb.model.DescribeEndpointsResponse result = _impl.describeEndpoints(converted);
      DescribeEndpointsResponse dafnyResponse = ToDafny.DescribeEndpointsResponse(result);
      return Result.create_Success(dafnyResponse);
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeExportOutput, Error> DescribeExport(DescribeExportInput input) {
    DescribeExportRequest converted = ToNative.DescribeExportInput(input);
    try {
      DescribeExportResponse result = _impl.describeExport(converted);
      DescribeExportOutput dafnyResponse = ToDafny.DescribeExportOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ExportNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeGlobalTableOutput, Error> DescribeGlobalTable(
      DescribeGlobalTableInput input) {
    DescribeGlobalTableRequest converted = ToNative.DescribeGlobalTableInput(input);
    try {
      DescribeGlobalTableResponse result = _impl.describeGlobalTable(converted);
      DescribeGlobalTableOutput dafnyResponse = ToDafny.DescribeGlobalTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (GlobalTableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeGlobalTableSettingsOutput, Error> DescribeGlobalTableSettings(
      DescribeGlobalTableSettingsInput input) {
    DescribeGlobalTableSettingsRequest converted = ToNative.DescribeGlobalTableSettingsInput(input);
    try {
      DescribeGlobalTableSettingsResponse result = _impl.describeGlobalTableSettings(converted);
      DescribeGlobalTableSettingsOutput dafnyResponse = ToDafny.DescribeGlobalTableSettingsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (GlobalTableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeImportOutput, Error> DescribeImport(DescribeImportInput input) {
    DescribeImportRequest converted = ToNative.DescribeImportInput(input);
    try {
      DescribeImportResponse result = _impl.describeImport(converted);
      DescribeImportOutput dafnyResponse = ToDafny.DescribeImportOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ImportNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeKinesisStreamingDestinationOutput, Error> DescribeKinesisStreamingDestination(
      DescribeKinesisStreamingDestinationInput input) {
    DescribeKinesisStreamingDestinationRequest converted = ToNative.DescribeKinesisStreamingDestinationInput(input);
    try {
      DescribeKinesisStreamingDestinationResponse result = _impl.describeKinesisStreamingDestination(converted);
      DescribeKinesisStreamingDestinationOutput dafnyResponse = ToDafny.DescribeKinesisStreamingDestinationOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeLimitsOutput, Error> DescribeLimits(DescribeLimitsInput input) {
    DescribeLimitsRequest converted = ToNative.DescribeLimitsInput(input);
    try {
      DescribeLimitsResponse result = _impl.describeLimits(converted);
      DescribeLimitsOutput dafnyResponse = ToDafny.DescribeLimitsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeTableOutput, Error> DescribeTable(DescribeTableInput input) {
    DescribeTableRequest converted = ToNative.DescribeTableInput(input);
    try {
      DescribeTableResponse result = _impl.describeTable(converted);
      DescribeTableOutput dafnyResponse = ToDafny.DescribeTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeTableReplicaAutoScalingOutput, Error> DescribeTableReplicaAutoScaling(
      DescribeTableReplicaAutoScalingInput input) {
    DescribeTableReplicaAutoScalingRequest converted = ToNative.DescribeTableReplicaAutoScalingInput(input);
    try {
      DescribeTableReplicaAutoScalingResponse result = _impl.describeTableReplicaAutoScaling(converted);
      DescribeTableReplicaAutoScalingOutput dafnyResponse = ToDafny.DescribeTableReplicaAutoScalingOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DescribeTimeToLiveOutput, Error> DescribeTimeToLive(DescribeTimeToLiveInput input) {
    DescribeTimeToLiveRequest converted = ToNative.DescribeTimeToLiveInput(input);
    try {
      DescribeTimeToLiveResponse result = _impl.describeTimeToLive(converted);
      DescribeTimeToLiveOutput dafnyResponse = ToDafny.DescribeTimeToLiveOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<DisableKinesisStreamingDestinationOutput, Error> DisableKinesisStreamingDestination(
      DisableKinesisStreamingDestinationInput input) {
    DisableKinesisStreamingDestinationRequest converted = ToNative.DisableKinesisStreamingDestinationInput(input);
    try {
      DisableKinesisStreamingDestinationResponse result = _impl.disableKinesisStreamingDestination(converted);
      DisableKinesisStreamingDestinationOutput dafnyResponse = ToDafny.DisableKinesisStreamingDestinationOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<EnableKinesisStreamingDestinationOutput, Error> EnableKinesisStreamingDestination(
      EnableKinesisStreamingDestinationInput input) {
    EnableKinesisStreamingDestinationRequest converted = ToNative.EnableKinesisStreamingDestinationInput(input);
    try {
      EnableKinesisStreamingDestinationResponse result = _impl.enableKinesisStreamingDestination(converted);
      EnableKinesisStreamingDestinationOutput dafnyResponse = ToDafny.EnableKinesisStreamingDestinationOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ExecuteStatementOutput, Error> ExecuteStatement(ExecuteStatementInput input) {
    ExecuteStatementRequest converted = ToNative.ExecuteStatementInput(input);
    try {
      ExecuteStatementResponse result = _impl.executeStatement(converted);
      ExecuteStatementOutput dafnyResponse = ToDafny.ExecuteStatementOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ConditionalCheckFailedException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DuplicateItemException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ItemCollectionSizeLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ExecuteTransactionOutput, Error> ExecuteTransaction(ExecuteTransactionInput input) {
    ExecuteTransactionRequest converted = ToNative.ExecuteTransactionInput(input);
    try {
      ExecuteTransactionResponse result = _impl.executeTransaction(converted);
      ExecuteTransactionOutput dafnyResponse = ToDafny.ExecuteTransactionOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (IdempotentParameterMismatchException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionCanceledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionInProgressException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ExportTableToPointInTimeOutput, Error> ExportTableToPointInTime(
      ExportTableToPointInTimeInput input) {
    ExportTableToPointInTimeRequest converted = ToNative.ExportTableToPointInTimeInput(input);
    try {
      ExportTableToPointInTimeResponse result = _impl.exportTableToPointInTime(converted);
      ExportTableToPointInTimeOutput dafnyResponse = ToDafny.ExportTableToPointInTimeOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ExportConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidExportTimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (PointInTimeRecoveryUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<GetItemOutput, Error> GetItem(GetItemInput input) {
    GetItemRequest converted = ToNative.GetItemInput(input);
    try {
      GetItemResponse result = _impl.getItem(converted);
      GetItemOutput dafnyResponse = ToDafny.GetItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ImportTableOutput, Error> ImportTable(ImportTableInput input) {
    ImportTableRequest converted = ToNative.ImportTableInput(input);
    try {
      ImportTableResponse result = _impl.importTable(converted);
      ImportTableOutput dafnyResponse = ToDafny.ImportTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ImportConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListBackupsOutput, Error> ListBackups(ListBackupsInput input) {
    ListBackupsRequest converted = ToNative.ListBackupsInput(input);
    try {
      ListBackupsResponse result = _impl.listBackups(converted);
      ListBackupsOutput dafnyResponse = ToDafny.ListBackupsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListContributorInsightsOutput, Error> ListContributorInsights(
      ListContributorInsightsInput input) {
    ListContributorInsightsRequest converted = ToNative.ListContributorInsightsInput(input);
    try {
      ListContributorInsightsResponse result = _impl.listContributorInsights(converted);
      ListContributorInsightsOutput dafnyResponse = ToDafny.ListContributorInsightsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListExportsOutput, Error> ListExports(ListExportsInput input) {
    ListExportsRequest converted = ToNative.ListExportsInput(input);
    try {
      ListExportsResponse result = _impl.listExports(converted);
      ListExportsOutput dafnyResponse = ToDafny.ListExportsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListGlobalTablesOutput, Error> ListGlobalTables(ListGlobalTablesInput input) {
    ListGlobalTablesRequest converted = ToNative.ListGlobalTablesInput(input);
    try {
      ListGlobalTablesResponse result = _impl.listGlobalTables(converted);
      ListGlobalTablesOutput dafnyResponse = ToDafny.ListGlobalTablesOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListImportsOutput, Error> ListImports(ListImportsInput input) {
    ListImportsRequest converted = ToNative.ListImportsInput(input);
    try {
      ListImportsResponse result = _impl.listImports(converted);
      ListImportsOutput dafnyResponse = ToDafny.ListImportsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListTablesOutput, Error> ListTables(ListTablesInput input) {
    ListTablesRequest converted = ToNative.ListTablesInput(input);
    try {
      ListTablesResponse result = _impl.listTables(converted);
      ListTablesOutput dafnyResponse = ToDafny.ListTablesOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ListTagsOfResourceOutput, Error> ListTagsOfResource(ListTagsOfResourceInput input) {
    ListTagsOfResourceRequest converted = ToNative.ListTagsOfResourceInput(input);
    try {
      ListTagsOfResourceResponse result = _impl.listTagsOfResource(converted);
      ListTagsOfResourceOutput dafnyResponse = ToDafny.ListTagsOfResourceOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<PutItemOutput, Error> PutItem(PutItemInput input) {
    PutItemRequest converted = ToNative.PutItemInput(input);
    try {
      PutItemResponse result = _impl.putItem(converted);
      PutItemOutput dafnyResponse = ToDafny.PutItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ConditionalCheckFailedException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ItemCollectionSizeLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<QueryOutput, Error> Query(QueryInput input) {
    QueryRequest converted = ToNative.QueryInput(input);
    try {
      QueryResponse result = _impl.query(converted);
      QueryOutput dafnyResponse = ToDafny.QueryOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<RestoreTableFromBackupOutput, Error> RestoreTableFromBackup(
      RestoreTableFromBackupInput input) {
    RestoreTableFromBackupRequest converted = ToNative.RestoreTableFromBackupInput(input);
    try {
      RestoreTableFromBackupResponse result = _impl.restoreTableFromBackup(converted);
      RestoreTableFromBackupOutput dafnyResponse = ToDafny.RestoreTableFromBackupOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (BackupInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (BackupNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableAlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<RestoreTableToPointInTimeOutput, Error> RestoreTableToPointInTime(
      RestoreTableToPointInTimeInput input) {
    RestoreTableToPointInTimeRequest converted = ToNative.RestoreTableToPointInTimeInput(input);
    try {
      RestoreTableToPointInTimeResponse result = _impl.restoreTableToPointInTime(converted);
      RestoreTableToPointInTimeOutput dafnyResponse = ToDafny.RestoreTableToPointInTimeOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InvalidRestoreTimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (PointInTimeRecoveryUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableAlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<ScanOutput, Error> Scan(ScanInput input) {
    ScanRequest converted = ToNative.ScanInput(input);
    try {
      ScanResponse result = _impl.scan(converted);
      ScanOutput dafnyResponse = ToDafny.ScanOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> TagResource(TagResourceInput input) {
    TagResourceRequest converted = ToNative.TagResourceInput(input);
    try {
      _impl.tagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<TransactGetItemsOutput, Error> TransactGetItems(TransactGetItemsInput input) {
    TransactGetItemsRequest converted = ToNative.TransactGetItemsInput(input);
    try {
      TransactGetItemsResponse result = _impl.transactGetItems(converted);
      TransactGetItemsOutput dafnyResponse = ToDafny.TransactGetItemsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionCanceledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<TransactWriteItemsOutput, Error> TransactWriteItems(TransactWriteItemsInput input) {
    TransactWriteItemsRequest converted = ToNative.TransactWriteItemsInput(input);
    try {
      TransactWriteItemsResponse result = _impl.transactWriteItems(converted);
      TransactWriteItemsOutput dafnyResponse = ToDafny.TransactWriteItemsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (IdempotentParameterMismatchException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionCanceledException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionInProgressException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<Tuple0, Error> UntagResource(UntagResourceInput input) {
    UntagResourceRequest converted = ToNative.UntagResourceInput(input);
    try {
      _impl.untagResource(converted);
      return Result.create_Success(Tuple0.create());
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateContinuousBackupsOutput, Error> UpdateContinuousBackups(
      UpdateContinuousBackupsInput input) {
    UpdateContinuousBackupsRequest converted = ToNative.UpdateContinuousBackupsInput(input);
    try {
      UpdateContinuousBackupsResponse result = _impl.updateContinuousBackups(converted);
      UpdateContinuousBackupsOutput dafnyResponse = ToDafny.UpdateContinuousBackupsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ContinuousBackupsUnavailableException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateContributorInsightsOutput, Error> UpdateContributorInsights(
      UpdateContributorInsightsInput input) {
    UpdateContributorInsightsRequest converted = ToNative.UpdateContributorInsightsInput(input);
    try {
      UpdateContributorInsightsResponse result = _impl.updateContributorInsights(converted);
      UpdateContributorInsightsOutput dafnyResponse = ToDafny.UpdateContributorInsightsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateGlobalTableOutput, Error> UpdateGlobalTable(UpdateGlobalTableInput input) {
    UpdateGlobalTableRequest converted = ToNative.UpdateGlobalTableInput(input);
    try {
      UpdateGlobalTableResponse result = _impl.updateGlobalTable(converted);
      UpdateGlobalTableOutput dafnyResponse = ToDafny.UpdateGlobalTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (GlobalTableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ReplicaAlreadyExistsException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ReplicaNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateGlobalTableSettingsOutput, Error> UpdateGlobalTableSettings(
      UpdateGlobalTableSettingsInput input) {
    UpdateGlobalTableSettingsRequest converted = ToNative.UpdateGlobalTableSettingsInput(input);
    try {
      UpdateGlobalTableSettingsResponse result = _impl.updateGlobalTableSettings(converted);
      UpdateGlobalTableSettingsOutput dafnyResponse = ToDafny.UpdateGlobalTableSettingsOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (GlobalTableNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (IndexNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ReplicaNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateItemOutput, Error> UpdateItem(UpdateItemInput input) {
    UpdateItemRequest converted = ToNative.UpdateItemInput(input);
    try {
      UpdateItemResponse result = _impl.updateItem(converted);
      UpdateItemOutput dafnyResponse = ToDafny.UpdateItemOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (ConditionalCheckFailedException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ItemCollectionSizeLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ProvisionedThroughputExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (RequestLimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (TransactionConflictException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateTableOutput, Error> UpdateTable(UpdateTableInput input) {
    UpdateTableRequest converted = ToNative.UpdateTableInput(input);
    try {
      UpdateTableResponse result = _impl.updateTable(converted);
      UpdateTableOutput dafnyResponse = ToDafny.UpdateTableOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateTableReplicaAutoScalingOutput, Error> UpdateTableReplicaAutoScaling(
      UpdateTableReplicaAutoScalingInput input) {
    UpdateTableReplicaAutoScalingRequest converted = ToNative.UpdateTableReplicaAutoScalingInput(input);
    try {
      UpdateTableReplicaAutoScalingResponse result = _impl.updateTableReplicaAutoScaling(converted);
      UpdateTableReplicaAutoScalingOutput dafnyResponse = ToDafny.UpdateTableReplicaAutoScalingOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  @Override
  public Result<UpdateTimeToLiveOutput, Error> UpdateTimeToLive(UpdateTimeToLiveInput input) {
    UpdateTimeToLiveRequest converted = ToNative.UpdateTimeToLiveInput(input);
    try {
      UpdateTimeToLiveResponse result = _impl.updateTimeToLive(converted);
      UpdateTimeToLiveOutput dafnyResponse = ToDafny.UpdateTimeToLiveOutput(result);
      return Result.create_Success(dafnyResponse);
    } catch (InternalServerErrorException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (LimitExceededException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceInUseException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (ResourceNotFoundException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (DynamoDbException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }
}
