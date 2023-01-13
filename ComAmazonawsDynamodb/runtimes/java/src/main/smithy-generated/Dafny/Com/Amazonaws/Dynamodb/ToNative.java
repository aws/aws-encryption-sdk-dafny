// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package Dafny.Com.Amazonaws.Dynamodb;

import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDB__20120810Client;
import software.amazon.awssdk.core.SdkBytes;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.dynamodb.model.ArchivalSummary;
import software.amazon.awssdk.services.dynamodb.model.AttributeAction;
import software.amazon.awssdk.services.dynamodb.model.AttributeDefinition;
import software.amazon.awssdk.services.dynamodb.model.AttributeValue;
import software.amazon.awssdk.services.dynamodb.model.AttributeValueUpdate;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingPolicyDescription;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingPolicyUpdate;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingSettingsDescription;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingTargetTrackingScalingPolicyConfigurationDescription;
import software.amazon.awssdk.services.dynamodb.model.AutoScalingTargetTrackingScalingPolicyConfigurationUpdate;
import software.amazon.awssdk.services.dynamodb.model.BackupDescription;
import software.amazon.awssdk.services.dynamodb.model.BackupDetails;
import software.amazon.awssdk.services.dynamodb.model.BackupStatus;
import software.amazon.awssdk.services.dynamodb.model.BackupSummary;
import software.amazon.awssdk.services.dynamodb.model.BackupType;
import software.amazon.awssdk.services.dynamodb.model.BackupTypeFilter;
import software.amazon.awssdk.services.dynamodb.model.BatchExecuteStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchExecuteStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.BatchGetItemRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchGetItemResponse;
import software.amazon.awssdk.services.dynamodb.model.BatchStatementError;
import software.amazon.awssdk.services.dynamodb.model.BatchStatementErrorCodeEnum;
import software.amazon.awssdk.services.dynamodb.model.BatchStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.BatchWriteItemRequest;
import software.amazon.awssdk.services.dynamodb.model.BatchWriteItemResponse;
import software.amazon.awssdk.services.dynamodb.model.BillingMode;
import software.amazon.awssdk.services.dynamodb.model.BillingModeSummary;
import software.amazon.awssdk.services.dynamodb.model.Capacity;
import software.amazon.awssdk.services.dynamodb.model.ComparisonOperator;
import software.amazon.awssdk.services.dynamodb.model.Condition;
import software.amazon.awssdk.services.dynamodb.model.ConditionCheck;
import software.amazon.awssdk.services.dynamodb.model.ConditionalOperator;
import software.amazon.awssdk.services.dynamodb.model.ConsumedCapacity;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsDescription;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsStatus;
import software.amazon.awssdk.services.dynamodb.model.ContributorInsightsAction;
import software.amazon.awssdk.services.dynamodb.model.ContributorInsightsStatus;
import software.amazon.awssdk.services.dynamodb.model.ContributorInsightsSummary;
import software.amazon.awssdk.services.dynamodb.model.CreateBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.CreateGlobalSecondaryIndexAction;
import software.amazon.awssdk.services.dynamodb.model.CreateGlobalTableRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateGlobalTableResponse;
import software.amazon.awssdk.services.dynamodb.model.CreateReplicaAction;
import software.amazon.awssdk.services.dynamodb.model.CreateReplicationGroupMemberAction;
import software.amazon.awssdk.services.dynamodb.model.CreateTableRequest;
import software.amazon.awssdk.services.dynamodb.model.CreateTableResponse;
import software.amazon.awssdk.services.dynamodb.model.CsvOptions;
import software.amazon.awssdk.services.dynamodb.model.Delete;
import software.amazon.awssdk.services.dynamodb.model.DeleteBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.DeleteGlobalSecondaryIndexAction;
import software.amazon.awssdk.services.dynamodb.model.DeleteItemRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteItemResponse;
import software.amazon.awssdk.services.dynamodb.model.DeleteReplicaAction;
import software.amazon.awssdk.services.dynamodb.model.DeleteReplicationGroupMemberAction;
import software.amazon.awssdk.services.dynamodb.model.DeleteRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DeleteTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeContinuousBackupsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeContinuousBackupsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeContributorInsightsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeContributorInsightsResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeEndpointsRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeEndpointsResponse;
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
import software.amazon.awssdk.services.dynamodb.model.DescribeTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveResponse;
import software.amazon.awssdk.services.dynamodb.model.DestinationStatus;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.Endpoint;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionResponse;
import software.amazon.awssdk.services.dynamodb.model.ExpectedAttributeValue;
import software.amazon.awssdk.services.dynamodb.model.ExportDescription;
import software.amazon.awssdk.services.dynamodb.model.ExportFormat;
import software.amazon.awssdk.services.dynamodb.model.ExportStatus;
import software.amazon.awssdk.services.dynamodb.model.ExportSummary;
import software.amazon.awssdk.services.dynamodb.model.ExportTableToPointInTimeRequest;
import software.amazon.awssdk.services.dynamodb.model.ExportTableToPointInTimeResponse;
import software.amazon.awssdk.services.dynamodb.model.FailureException;
import software.amazon.awssdk.services.dynamodb.model.Get;
import software.amazon.awssdk.services.dynamodb.model.GetItemRequest;
import software.amazon.awssdk.services.dynamodb.model.GetItemResponse;
import software.amazon.awssdk.services.dynamodb.model.GlobalSecondaryIndex;
import software.amazon.awssdk.services.dynamodb.model.GlobalSecondaryIndexAutoScalingUpdate;
import software.amazon.awssdk.services.dynamodb.model.GlobalSecondaryIndexDescription;
import software.amazon.awssdk.services.dynamodb.model.GlobalSecondaryIndexInfo;
import software.amazon.awssdk.services.dynamodb.model.GlobalSecondaryIndexUpdate;
import software.amazon.awssdk.services.dynamodb.model.GlobalTable;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableDescription;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableGlobalSecondaryIndexSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableStatus;
import software.amazon.awssdk.services.dynamodb.model.ImportStatus;
import software.amazon.awssdk.services.dynamodb.model.ImportSummary;
import software.amazon.awssdk.services.dynamodb.model.ImportTableDescription;
import software.amazon.awssdk.services.dynamodb.model.ImportTableRequest;
import software.amazon.awssdk.services.dynamodb.model.ImportTableResponse;
import software.amazon.awssdk.services.dynamodb.model.IndexStatus;
import software.amazon.awssdk.services.dynamodb.model.InputCompressionType;
import software.amazon.awssdk.services.dynamodb.model.InputFormat;
import software.amazon.awssdk.services.dynamodb.model.InputFormatOptions;
import software.amazon.awssdk.services.dynamodb.model.ItemCollectionMetrics;
import software.amazon.awssdk.services.dynamodb.model.ItemResponse;
import software.amazon.awssdk.services.dynamodb.model.KeySchemaElement;
import software.amazon.awssdk.services.dynamodb.model.KeyType;
import software.amazon.awssdk.services.dynamodb.model.KeysAndAttributes;
import software.amazon.awssdk.services.dynamodb.model.KinesisDataStreamDestination;
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
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndex;
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndexDescription;
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndexInfo;
import software.amazon.awssdk.services.dynamodb.model.ParameterizedStatement;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryDescription;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoverySpecification;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryStatus;
import software.amazon.awssdk.services.dynamodb.model.Projection;
import software.amazon.awssdk.services.dynamodb.model.ProjectionType;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughput;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputDescription;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputOverride;
import software.amazon.awssdk.services.dynamodb.model.Put;
import software.amazon.awssdk.services.dynamodb.model.PutItemRequest;
import software.amazon.awssdk.services.dynamodb.model.PutItemResponse;
import software.amazon.awssdk.services.dynamodb.model.PutRequest;
import software.amazon.awssdk.services.dynamodb.model.QueryRequest;
import software.amazon.awssdk.services.dynamodb.model.QueryResponse;
import software.amazon.awssdk.services.dynamodb.model.Replica;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAutoScalingUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndex;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexAutoScalingUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexSettingsDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaSettingsDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaStatus;
import software.amazon.awssdk.services.dynamodb.model.ReplicaUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicationGroupUpdate;
import software.amazon.awssdk.services.dynamodb.model.RestoreSummary;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableFromBackupRequest;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableFromBackupResponse;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableToPointInTimeRequest;
import software.amazon.awssdk.services.dynamodb.model.RestoreTableToPointInTimeResponse;
import software.amazon.awssdk.services.dynamodb.model.ReturnConsumedCapacity;
import software.amazon.awssdk.services.dynamodb.model.ReturnItemCollectionMetrics;
import software.amazon.awssdk.services.dynamodb.model.ReturnValue;
import software.amazon.awssdk.services.dynamodb.model.ReturnValuesOnConditionCheckFailure;
import software.amazon.awssdk.services.dynamodb.model.S3BucketSource;
import software.amazon.awssdk.services.dynamodb.model.S3SseAlgorithm;
import software.amazon.awssdk.services.dynamodb.model.SSEDescription;
import software.amazon.awssdk.services.dynamodb.model.SSESpecification;
import software.amazon.awssdk.services.dynamodb.model.SSEStatus;
import software.amazon.awssdk.services.dynamodb.model.SSEType;
import software.amazon.awssdk.services.dynamodb.model.ScalarAttributeType;
import software.amazon.awssdk.services.dynamodb.model.ScanRequest;
import software.amazon.awssdk.services.dynamodb.model.ScanResponse;
import software.amazon.awssdk.services.dynamodb.model.Select;
import software.amazon.awssdk.services.dynamodb.model.SourceTableDetails;
import software.amazon.awssdk.services.dynamodb.model.SourceTableFeatureDetails;
import software.amazon.awssdk.services.dynamodb.model.StreamSpecification;
import software.amazon.awssdk.services.dynamodb.model.StreamViewType;
import software.amazon.awssdk.services.dynamodb.model.TableAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.TableClass;
import software.amazon.awssdk.services.dynamodb.model.TableClassSummary;
import software.amazon.awssdk.services.dynamodb.model.TableCreationParameters;
import software.amazon.awssdk.services.dynamodb.model.TableDescription;
import software.amazon.awssdk.services.dynamodb.model.TableStatus;
import software.amazon.awssdk.services.dynamodb.model.Tag;
import software.amazon.awssdk.services.dynamodb.model.TagResourceRequest;
import software.amazon.awssdk.services.dynamodb.model.TimeToLiveDescription;
import software.amazon.awssdk.services.dynamodb.model.TimeToLiveSpecification;
import software.amazon.awssdk.services.dynamodb.model.TimeToLiveStatus;
import software.amazon.awssdk.services.dynamodb.model.TransactGetItem;
import software.amazon.awssdk.services.dynamodb.model.TransactGetItemsRequest;
import software.amazon.awssdk.services.dynamodb.model.TransactGetItemsResponse;
import software.amazon.awssdk.services.dynamodb.model.TransactWriteItem;
import software.amazon.awssdk.services.dynamodb.model.TransactWriteItemsRequest;
import software.amazon.awssdk.services.dynamodb.model.TransactWriteItemsResponse;
import software.amazon.awssdk.services.dynamodb.model.UntagResourceRequest;
import software.amazon.awssdk.services.dynamodb.model.Update;
import software.amazon.awssdk.services.dynamodb.model.UpdateContinuousBackupsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateContinuousBackupsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateContributorInsightsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateContributorInsightsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalSecondaryIndexAction;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableSettingsRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateGlobalTableSettingsResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateItemRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateItemResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateReplicationGroupMemberAction;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveResponse;
import software.amazon.awssdk.services.dynamodb.model.WriteRequest;
import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Integer;
import java.lang.String;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ToNative {
  public static BatchExecuteStatementResponse BatchExecuteStatementOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchExecuteStatementOutput dafnyValue) {
    BatchExecuteStatementResponse.Builder nativeBuilder = BatchExecuteStatementResponse.builder();
    if (dafnyValue.dtor_Responses().is_Some()) {
      nativeBuilder.responses(ToNative.PartiQLBatchResponse(dafnyValue.dtor_Responses().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static BatchGetItemResponse BatchGetItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.BatchGetItemOutput dafnyValue) {
    BatchGetItemResponse.Builder nativeBuilder = BatchGetItemResponse.builder();
    if (dafnyValue.dtor_Responses().is_Some()) {
      nativeBuilder.responses(ToNative.BatchGetResponseMap(dafnyValue.dtor_Responses().dtor_value()));
    }
    if (dafnyValue.dtor_UnprocessedKeys().is_Some()) {
      nativeBuilder.unprocessedKeys(ToNative.BatchGetRequestMap(dafnyValue.dtor_UnprocessedKeys().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static BatchWriteItemResponse BatchWriteItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.BatchWriteItemOutput dafnyValue) {
    BatchWriteItemResponse.Builder nativeBuilder = BatchWriteItemResponse.builder();
    if (dafnyValue.dtor_UnprocessedItems().is_Some()) {
      nativeBuilder.unprocessedItems(ToNative.BatchWriteItemRequestMap(dafnyValue.dtor_UnprocessedItems().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      nativeBuilder.itemCollectionMetrics(ToNative.ItemCollectionMetricsPerTable(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateBackupResponse CreateBackupOutput(Dafny.Com.Amazonaws.Dynamodb.Types.CreateBackupOutput dafnyValue) {
    CreateBackupResponse.Builder nativeBuilder = CreateBackupResponse.builder();
    if (dafnyValue.dtor_BackupDetails().is_Some()) {
      nativeBuilder.backupDetails(ToNative.BackupDetails(dafnyValue.dtor_BackupDetails().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateGlobalTableResponse CreateGlobalTableOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateGlobalTableOutput dafnyValue) {
    CreateGlobalTableResponse.Builder nativeBuilder = CreateGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      nativeBuilder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateTableResponse CreateTableOutput(Dafny.Com.Amazonaws.Dynamodb.Types.CreateTableOutput dafnyValue) {
    CreateTableResponse.Builder nativeBuilder = CreateTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      nativeBuilder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DeleteBackupResponse DeleteBackupOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DeleteBackupOutput dafnyValue) {
    DeleteBackupResponse.Builder nativeBuilder = DeleteBackupResponse.builder();
    if (dafnyValue.dtor_BackupDescription().is_Some()) {
      nativeBuilder.backupDescription(ToNative.BackupDescription(dafnyValue.dtor_BackupDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DeleteItemResponse DeleteItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DeleteItemOutput dafnyValue) {
    DeleteItemResponse.Builder nativeBuilder = DeleteItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      nativeBuilder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      nativeBuilder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DeleteTableResponse DeleteTableOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DeleteTableOutput dafnyValue) {
    DeleteTableResponse.Builder nativeBuilder = DeleteTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      nativeBuilder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeBackupResponse DescribeBackupOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DescribeBackupOutput dafnyValue) {
    DescribeBackupResponse.Builder nativeBuilder = DescribeBackupResponse.builder();
    if (dafnyValue.dtor_BackupDescription().is_Some()) {
      nativeBuilder.backupDescription(ToNative.BackupDescription(dafnyValue.dtor_BackupDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeContinuousBackupsResponse DescribeContinuousBackupsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeContinuousBackupsOutput dafnyValue) {
    DescribeContinuousBackupsResponse.Builder nativeBuilder = DescribeContinuousBackupsResponse.builder();
    if (dafnyValue.dtor_ContinuousBackupsDescription().is_Some()) {
      nativeBuilder.continuousBackupsDescription(ToNative.ContinuousBackupsDescription(dafnyValue.dtor_ContinuousBackupsDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeContributorInsightsResponse DescribeContributorInsightsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeContributorInsightsOutput dafnyValue) {
    DescribeContributorInsightsResponse.Builder nativeBuilder = DescribeContributorInsightsResponse.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      nativeBuilder.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      nativeBuilder.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ContributorInsightsRuleList().is_Some()) {
      nativeBuilder.contributorInsightsRuleList(ToNative.ContributorInsightsRuleList(dafnyValue.dtor_ContributorInsightsRuleList().dtor_value()));
    }
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      nativeBuilder.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdateDateTime().is_Some()) {
      nativeBuilder.lastUpdateDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LastUpdateDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_FailureException().is_Some()) {
      nativeBuilder.failureException(ToNative.FailureException(dafnyValue.dtor_FailureException().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeEndpointsResponse DescribeEndpointsResponse(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeEndpointsResponse dafnyValue) {
    DescribeEndpointsResponse.Builder nativeBuilder = DescribeEndpointsResponse.builder();
    nativeBuilder.endpoints(ToNative.Endpoints(dafnyValue.dtor_Endpoints()));
    return nativeBuilder.build();
  }

  public static DescribeExportResponse DescribeExportOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DescribeExportOutput dafnyValue) {
    DescribeExportResponse.Builder nativeBuilder = DescribeExportResponse.builder();
    if (dafnyValue.dtor_ExportDescription().is_Some()) {
      nativeBuilder.exportDescription(ToNative.ExportDescription(dafnyValue.dtor_ExportDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeGlobalTableResponse DescribeGlobalTableOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeGlobalTableOutput dafnyValue) {
    DescribeGlobalTableResponse.Builder nativeBuilder = DescribeGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      nativeBuilder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeGlobalTableSettingsResponse DescribeGlobalTableSettingsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeGlobalTableSettingsOutput dafnyValue) {
    DescribeGlobalTableSettingsResponse.Builder nativeBuilder = DescribeGlobalTableSettingsResponse.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      nativeBuilder.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettings().is_Some()) {
      nativeBuilder.replicaSettings(ToNative.ReplicaSettingsDescriptionList(dafnyValue.dtor_ReplicaSettings().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeImportResponse DescribeImportOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DescribeImportOutput dafnyValue) {
    DescribeImportResponse.Builder nativeBuilder = DescribeImportResponse.builder();
    nativeBuilder.importTableDescription(ToNative.ImportTableDescription(dafnyValue.dtor_ImportTableDescription()));
    return nativeBuilder.build();
  }

  public static DescribeKinesisStreamingDestinationResponse DescribeKinesisStreamingDestinationOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeKinesisStreamingDestinationOutput dafnyValue) {
    DescribeKinesisStreamingDestinationResponse.Builder nativeBuilder = DescribeKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      nativeBuilder.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_KinesisDataStreamDestinations().is_Some()) {
      nativeBuilder.kinesisDataStreamDestinations(ToNative.KinesisDataStreamDestinations(dafnyValue.dtor_KinesisDataStreamDestinations().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeLimitsResponse DescribeLimitsOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DescribeLimitsOutput dafnyValue) {
    DescribeLimitsResponse.Builder nativeBuilder = DescribeLimitsResponse.builder();
    if (dafnyValue.dtor_AccountMaxReadCapacityUnits().is_Some()) {
      nativeBuilder.accountMaxReadCapacityUnits((dafnyValue.dtor_AccountMaxReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_AccountMaxWriteCapacityUnits().is_Some()) {
      nativeBuilder.accountMaxWriteCapacityUnits((dafnyValue.dtor_AccountMaxWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_TableMaxReadCapacityUnits().is_Some()) {
      nativeBuilder.tableMaxReadCapacityUnits((dafnyValue.dtor_TableMaxReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_TableMaxWriteCapacityUnits().is_Some()) {
      nativeBuilder.tableMaxWriteCapacityUnits((dafnyValue.dtor_TableMaxWriteCapacityUnits().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeTableResponse DescribeTableOutput(Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTableOutput dafnyValue) {
    DescribeTableResponse.Builder nativeBuilder = DescribeTableResponse.builder();
    if (dafnyValue.dtor_Table().is_Some()) {
      nativeBuilder.table(ToNative.TableDescription(dafnyValue.dtor_Table().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeTableReplicaAutoScalingResponse DescribeTableReplicaAutoScalingOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTableReplicaAutoScalingOutput dafnyValue) {
    DescribeTableReplicaAutoScalingResponse.Builder nativeBuilder = DescribeTableReplicaAutoScalingResponse.builder();
    if (dafnyValue.dtor_TableAutoScalingDescription().is_Some()) {
      nativeBuilder.tableAutoScalingDescription(ToNative.TableAutoScalingDescription(dafnyValue.dtor_TableAutoScalingDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DescribeTimeToLiveResponse DescribeTimeToLiveOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTimeToLiveOutput dafnyValue) {
    DescribeTimeToLiveResponse.Builder nativeBuilder = DescribeTimeToLiveResponse.builder();
    if (dafnyValue.dtor_TimeToLiveDescription().is_Some()) {
      nativeBuilder.timeToLiveDescription(ToNative.TimeToLiveDescription(dafnyValue.dtor_TimeToLiveDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static DisableKinesisStreamingDestinationResponse DisableKinesisStreamingDestinationOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DisableKinesisStreamingDestinationOutput dafnyValue) {
    DisableKinesisStreamingDestinationResponse.Builder nativeBuilder = DisableKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      nativeBuilder.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      nativeBuilder.streamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      nativeBuilder.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static EnableKinesisStreamingDestinationResponse EnableKinesisStreamingDestinationOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.EnableKinesisStreamingDestinationOutput dafnyValue) {
    EnableKinesisStreamingDestinationResponse.Builder nativeBuilder = EnableKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      nativeBuilder.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      nativeBuilder.streamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      nativeBuilder.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ExecuteStatementResponse ExecuteStatementOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ExecuteStatementOutput dafnyValue) {
    ExecuteStatementResponse.Builder nativeBuilder = ExecuteStatementResponse.builder();
    if (dafnyValue.dtor_Items().is_Some()) {
      nativeBuilder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      nativeBuilder.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      nativeBuilder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ExecuteTransactionResponse ExecuteTransactionOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExecuteTransactionOutput dafnyValue) {
    ExecuteTransactionResponse.Builder nativeBuilder = ExecuteTransactionResponse.builder();
    if (dafnyValue.dtor_Responses().is_Some()) {
      nativeBuilder.responses(ToNative.ItemResponseList(dafnyValue.dtor_Responses().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ExportTableToPointInTimeResponse ExportTableToPointInTimeOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportTableToPointInTimeOutput dafnyValue) {
    ExportTableToPointInTimeResponse.Builder nativeBuilder = ExportTableToPointInTimeResponse.builder();
    if (dafnyValue.dtor_ExportDescription().is_Some()) {
      nativeBuilder.exportDescription(ToNative.ExportDescription(dafnyValue.dtor_ExportDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetItemResponse GetItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.GetItemOutput dafnyValue) {
    GetItemResponse.Builder nativeBuilder = GetItemResponse.builder();
    if (dafnyValue.dtor_Item().is_Some()) {
      nativeBuilder.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ImportTableResponse ImportTableOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ImportTableOutput dafnyValue) {
    ImportTableResponse.Builder nativeBuilder = ImportTableResponse.builder();
    nativeBuilder.importTableDescription(ToNative.ImportTableDescription(dafnyValue.dtor_ImportTableDescription()));
    return nativeBuilder.build();
  }

  public static ListBackupsResponse ListBackupsOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ListBackupsOutput dafnyValue) {
    ListBackupsResponse.Builder nativeBuilder = ListBackupsResponse.builder();
    if (dafnyValue.dtor_BackupSummaries().is_Some()) {
      nativeBuilder.backupSummaries(ToNative.BackupSummaries(dafnyValue.dtor_BackupSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedBackupArn().is_Some()) {
      nativeBuilder.lastEvaluatedBackupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedBackupArn().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListContributorInsightsResponse ListContributorInsightsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListContributorInsightsOutput dafnyValue) {
    ListContributorInsightsResponse.Builder nativeBuilder = ListContributorInsightsResponse.builder();
    if (dafnyValue.dtor_ContributorInsightsSummaries().is_Some()) {
      nativeBuilder.contributorInsightsSummaries(ToNative.ContributorInsightsSummaries(dafnyValue.dtor_ContributorInsightsSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      nativeBuilder.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListExportsResponse ListExportsOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ListExportsOutput dafnyValue) {
    ListExportsResponse.Builder nativeBuilder = ListExportsResponse.builder();
    if (dafnyValue.dtor_ExportSummaries().is_Some()) {
      nativeBuilder.exportSummaries(ToNative.ExportSummaries(dafnyValue.dtor_ExportSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      nativeBuilder.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListGlobalTablesResponse ListGlobalTablesOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ListGlobalTablesOutput dafnyValue) {
    ListGlobalTablesResponse.Builder nativeBuilder = ListGlobalTablesResponse.builder();
    if (dafnyValue.dtor_GlobalTables().is_Some()) {
      nativeBuilder.globalTables(ToNative.GlobalTableList(dafnyValue.dtor_GlobalTables().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedGlobalTableName().is_Some()) {
      nativeBuilder.lastEvaluatedGlobalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedGlobalTableName().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListImportsResponse ListImportsOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ListImportsOutput dafnyValue) {
    ListImportsResponse.Builder nativeBuilder = ListImportsResponse.builder();
    if (dafnyValue.dtor_ImportSummaryList().is_Some()) {
      nativeBuilder.importSummaryList(ToNative.ImportSummaryList(dafnyValue.dtor_ImportSummaryList().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      nativeBuilder.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListTablesResponse ListTablesOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ListTablesOutput dafnyValue) {
    ListTablesResponse.Builder nativeBuilder = ListTablesResponse.builder();
    if (dafnyValue.dtor_TableNames().is_Some()) {
      nativeBuilder.tableNames(ToNative.TableNameList(dafnyValue.dtor_TableNames().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedTableName().is_Some()) {
      nativeBuilder.lastEvaluatedTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedTableName().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ListTagsOfResourceResponse ListTagsOfResourceOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListTagsOfResourceOutput dafnyValue) {
    ListTagsOfResourceResponse.Builder nativeBuilder = ListTagsOfResourceResponse.builder();
    if (dafnyValue.dtor_Tags().is_Some()) {
      nativeBuilder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      nativeBuilder.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static PutItemResponse PutItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.PutItemOutput dafnyValue) {
    PutItemResponse.Builder nativeBuilder = PutItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      nativeBuilder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      nativeBuilder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static QueryResponse QueryOutput(Dafny.Com.Amazonaws.Dynamodb.Types.QueryOutput dafnyValue) {
    QueryResponse.Builder nativeBuilder = QueryResponse.builder();
    if (dafnyValue.dtor_Items().is_Some()) {
      nativeBuilder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_Count().is_Some()) {
      nativeBuilder.count((dafnyValue.dtor_Count().dtor_value()));
    }
    if (dafnyValue.dtor_ScannedCount().is_Some()) {
      nativeBuilder.scannedCount((dafnyValue.dtor_ScannedCount().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      nativeBuilder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static RestoreTableFromBackupResponse RestoreTableFromBackupOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.RestoreTableFromBackupOutput dafnyValue) {
    RestoreTableFromBackupResponse.Builder nativeBuilder = RestoreTableFromBackupResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      nativeBuilder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static RestoreTableToPointInTimeResponse RestoreTableToPointInTimeOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.RestoreTableToPointInTimeOutput dafnyValue) {
    RestoreTableToPointInTimeResponse.Builder nativeBuilder = RestoreTableToPointInTimeResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      nativeBuilder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static ScanResponse ScanOutput(Dafny.Com.Amazonaws.Dynamodb.Types.ScanOutput dafnyValue) {
    ScanResponse.Builder nativeBuilder = ScanResponse.builder();
    if (dafnyValue.dtor_Items().is_Some()) {
      nativeBuilder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_Count().is_Some()) {
      nativeBuilder.count((dafnyValue.dtor_Count().dtor_value()));
    }
    if (dafnyValue.dtor_ScannedCount().is_Some()) {
      nativeBuilder.scannedCount((dafnyValue.dtor_ScannedCount().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      nativeBuilder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static TransactGetItemsResponse TransactGetItemsOutput(Dafny.Com.Amazonaws.Dynamodb.Types.TransactGetItemsOutput dafnyValue) {
    TransactGetItemsResponse.Builder nativeBuilder = TransactGetItemsResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Responses().is_Some()) {
      nativeBuilder.responses(ToNative.ItemResponseList(dafnyValue.dtor_Responses().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static TransactWriteItemsResponse TransactWriteItemsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.TransactWriteItemsOutput dafnyValue) {
    TransactWriteItemsResponse.Builder nativeBuilder = TransactWriteItemsResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      nativeBuilder.itemCollectionMetrics(ToNative.ItemCollectionMetricsPerTable(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateContinuousBackupsResponse UpdateContinuousBackupsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateContinuousBackupsOutput dafnyValue) {
    UpdateContinuousBackupsResponse.Builder nativeBuilder = UpdateContinuousBackupsResponse.builder();
    if (dafnyValue.dtor_ContinuousBackupsDescription().is_Some()) {
      nativeBuilder.continuousBackupsDescription(ToNative.ContinuousBackupsDescription(dafnyValue.dtor_ContinuousBackupsDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateContributorInsightsResponse UpdateContributorInsightsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateContributorInsightsOutput dafnyValue) {
    UpdateContributorInsightsResponse.Builder nativeBuilder = UpdateContributorInsightsResponse.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      nativeBuilder.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      nativeBuilder.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      nativeBuilder.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateGlobalTableResponse UpdateGlobalTableOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateGlobalTableOutput dafnyValue) {
    UpdateGlobalTableResponse.Builder nativeBuilder = UpdateGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      nativeBuilder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateGlobalTableSettingsResponse UpdateGlobalTableSettingsOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateGlobalTableSettingsOutput dafnyValue) {
    UpdateGlobalTableSettingsResponse.Builder nativeBuilder = UpdateGlobalTableSettingsResponse.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      nativeBuilder.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettings().is_Some()) {
      nativeBuilder.replicaSettings(ToNative.ReplicaSettingsDescriptionList(dafnyValue.dtor_ReplicaSettings().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateItemResponse UpdateItemOutput(Dafny.Com.Amazonaws.Dynamodb.Types.UpdateItemOutput dafnyValue) {
    UpdateItemResponse.Builder nativeBuilder = UpdateItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      nativeBuilder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      nativeBuilder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      nativeBuilder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateTableResponse UpdateTableOutput(Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTableOutput dafnyValue) {
    UpdateTableResponse.Builder nativeBuilder = UpdateTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      nativeBuilder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateTableReplicaAutoScalingResponse UpdateTableReplicaAutoScalingOutput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTableReplicaAutoScalingOutput dafnyValue) {
    UpdateTableReplicaAutoScalingResponse.Builder nativeBuilder = UpdateTableReplicaAutoScalingResponse.builder();
    if (dafnyValue.dtor_TableAutoScalingDescription().is_Some()) {
      nativeBuilder.tableAutoScalingDescription(ToNative.TableAutoScalingDescription(dafnyValue.dtor_TableAutoScalingDescription().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UpdateTimeToLiveResponse UpdateTimeToLiveOutput(Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTimeToLiveOutput dafnyValue) {
    UpdateTimeToLiveResponse.Builder nativeBuilder = UpdateTimeToLiveResponse.builder();
    if (dafnyValue.dtor_TimeToLiveSpecification().is_Some()) {
      nativeBuilder.timeToLiveSpecification(ToNative.TimeToLiveSpecification(dafnyValue.dtor_TimeToLiveSpecification().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static BatchExecuteStatementRequest BatchExecuteStatementInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchExecuteStatementInput dafnyValue) {
    BatchExecuteStatementRequest.Builder converted = BatchExecuteStatementRequest.builder();
    converted.statements(ToNative.PartiQLBatchRequest(dafnyValue.dtor_Statements()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    return converted.build();
  }

  public static BatchGetItemRequest BatchGetItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchGetItemInput dafnyValue) {
    BatchGetItemRequest.Builder converted = BatchGetItemRequest.builder();
    converted.requestItems(ToNative.BatchGetRequestMap(dafnyValue.dtor_RequestItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    return converted.build();
  }

  public static BatchWriteItemRequest BatchWriteItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchWriteItemInput dafnyValue) {
    BatchWriteItemRequest.Builder converted = BatchWriteItemRequest.builder();
    converted.requestItems(ToNative.BatchWriteItemRequestMap(dafnyValue.dtor_RequestItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      converted.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    return converted.build();
  }

  public static CreateBackupRequest CreateBackupInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateBackupInput dafnyValue) {
    CreateBackupRequest.Builder converted = CreateBackupRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.backupName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName()));
    return converted.build();
  }

  public static CreateGlobalTableRequest CreateGlobalTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateGlobalTableInput dafnyValue) {
    CreateGlobalTableRequest.Builder converted = CreateGlobalTableRequest.builder();
    converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    converted.replicationGroup(ToNative.ReplicaList(dafnyValue.dtor_ReplicationGroup()));
    return converted.build();
  }

  public static CreateTableRequest CreateTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateTableInput dafnyValue) {
    CreateTableRequest.Builder converted = CreateTableRequest.builder();
    converted.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      converted.localSecondaryIndexes(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      converted.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      converted.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      converted.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      converted.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    if (dafnyValue.dtor_TableClass().is_Some()) {
      converted.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    return converted.build();
  }

  public static DeleteBackupRequest DeleteBackupInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteBackupInput dafnyValue) {
    DeleteBackupRequest.Builder converted = DeleteBackupRequest.builder();
    converted.backupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    return converted.build();
  }

  public static DeleteItemRequest DeleteItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteItemInput dafnyValue) {
    DeleteItemRequest.Builder converted = DeleteItemRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_Expected().is_Some()) {
      converted.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      converted.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      converted.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      converted.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    return converted.build();
  }

  public static DeleteTableRequest DeleteTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteTableInput dafnyValue) {
    DeleteTableRequest.Builder converted = DeleteTableRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DescribeBackupRequest DescribeBackupInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeBackupInput dafnyValue) {
    DescribeBackupRequest.Builder converted = DescribeBackupRequest.builder();
    converted.backupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    return converted.build();
  }

  public static DescribeContinuousBackupsRequest DescribeContinuousBackupsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeContinuousBackupsInput dafnyValue) {
    DescribeContinuousBackupsRequest.Builder converted = DescribeContinuousBackupsRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DescribeContributorInsightsRequest DescribeContributorInsightsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeContributorInsightsInput dafnyValue) {
    DescribeContributorInsightsRequest.Builder converted = DescribeContributorInsightsRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    return converted.build();
  }

  public static DescribeEndpointsRequest DescribeEndpointsRequest(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeEndpointsRequest dafnyValue) {
    return DescribeEndpointsRequest.builder().build();
  }

  public static DescribeExportRequest DescribeExportInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeExportInput dafnyValue) {
    DescribeExportRequest.Builder converted = DescribeExportRequest.builder();
    converted.exportArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn()));
    return converted.build();
  }

  public static DescribeGlobalTableRequest DescribeGlobalTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeGlobalTableInput dafnyValue) {
    DescribeGlobalTableRequest.Builder converted = DescribeGlobalTableRequest.builder();
    converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    return converted.build();
  }

  public static DescribeGlobalTableSettingsRequest DescribeGlobalTableSettingsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeGlobalTableSettingsInput dafnyValue) {
    DescribeGlobalTableSettingsRequest.Builder converted = DescribeGlobalTableSettingsRequest.builder();
    converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    return converted.build();
  }

  public static DescribeImportRequest DescribeImportInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeImportInput dafnyValue) {
    DescribeImportRequest.Builder converted = DescribeImportRequest.builder();
    converted.importArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn()));
    return converted.build();
  }

  public static DescribeKinesisStreamingDestinationRequest DescribeKinesisStreamingDestinationInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeKinesisStreamingDestinationInput dafnyValue) {
    DescribeKinesisStreamingDestinationRequest.Builder converted = DescribeKinesisStreamingDestinationRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DescribeLimitsRequest DescribeLimitsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeLimitsInput dafnyValue) {
    return DescribeLimitsRequest.builder().build();
  }

  public static DescribeTableRequest DescribeTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTableInput dafnyValue) {
    DescribeTableRequest.Builder converted = DescribeTableRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DescribeTableReplicaAutoScalingRequest DescribeTableReplicaAutoScalingInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTableReplicaAutoScalingInput dafnyValue) {
    DescribeTableReplicaAutoScalingRequest.Builder converted = DescribeTableReplicaAutoScalingRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DescribeTimeToLiveRequest DescribeTimeToLiveInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DescribeTimeToLiveInput dafnyValue) {
    DescribeTimeToLiveRequest.Builder converted = DescribeTimeToLiveRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return converted.build();
  }

  public static DisableKinesisStreamingDestinationRequest DisableKinesisStreamingDestinationInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.DisableKinesisStreamingDestinationInput dafnyValue) {
    DisableKinesisStreamingDestinationRequest.Builder converted = DisableKinesisStreamingDestinationRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.streamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn()));
    return converted.build();
  }

  public static EnableKinesisStreamingDestinationRequest EnableKinesisStreamingDestinationInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.EnableKinesisStreamingDestinationInput dafnyValue) {
    EnableKinesisStreamingDestinationRequest.Builder converted = EnableKinesisStreamingDestinationRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.streamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn()));
    return converted.build();
  }

  public static ExecuteStatementRequest ExecuteStatementInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExecuteStatementInput dafnyValue) {
    ExecuteStatementRequest.Builder converted = ExecuteStatementRequest.builder();
    converted.statement(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    if (dafnyValue.dtor_Parameters().is_Some()) {
      converted.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      converted.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    return converted.build();
  }

  public static ExecuteTransactionRequest ExecuteTransactionInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExecuteTransactionInput dafnyValue) {
    ExecuteTransactionRequest.Builder converted = ExecuteTransactionRequest.builder();
    converted.transactStatements(ToNative.ParameterizedStatements(dafnyValue.dtor_TransactStatements()));
    if (dafnyValue.dtor_ClientRequestToken().is_Some()) {
      converted.clientRequestToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientRequestToken().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    return converted.build();
  }

  public static ExportTableToPointInTimeRequest ExportTableToPointInTimeInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportTableToPointInTimeInput dafnyValue) {
    ExportTableToPointInTimeRequest.Builder converted = ExportTableToPointInTimeRequest.builder();
    converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn()));
    if (dafnyValue.dtor_ExportTime().is_Some()) {
      converted.exportTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_ExportTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      converted.clientToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    converted.s3Bucket(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket()));
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      converted.s3BucketOwner(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    if (dafnyValue.dtor_S3Prefix().is_Some()) {
      converted.s3Prefix(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Prefix().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseAlgorithm().is_Some()) {
      converted.s3SseAlgorithm(ToNative.S3SseAlgorithm(dafnyValue.dtor_S3SseAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseKmsKeyId().is_Some()) {
      converted.s3SseKmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3SseKmsKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ExportFormat().is_Some()) {
      converted.exportFormat(ToNative.ExportFormat(dafnyValue.dtor_ExportFormat().dtor_value()));
    }
    return converted.build();
  }

  public static GetItemRequest GetItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.GetItemInput dafnyValue) {
    GetItemRequest.Builder converted = GetItemRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      converted.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      converted.projectionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    return converted.build();
  }

  public static ImportTableRequest ImportTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ImportTableInput dafnyValue) {
    ImportTableRequest.Builder converted = ImportTableRequest.builder();
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      converted.clientToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    converted.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource()));
    converted.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat()));
    if (dafnyValue.dtor_InputFormatOptions().is_Some()) {
      converted.inputFormatOptions(ToNative.InputFormatOptions(dafnyValue.dtor_InputFormatOptions().dtor_value()));
    }
    if (dafnyValue.dtor_InputCompressionType().is_Some()) {
      converted.inputCompressionType(ToNative.InputCompressionType(dafnyValue.dtor_InputCompressionType().dtor_value()));
    }
    converted.tableCreationParameters(ToNative.TableCreationParameters(dafnyValue.dtor_TableCreationParameters()));
    return converted.build();
  }

  public static ListBackupsRequest ListBackupsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListBackupsInput dafnyValue) {
    ListBackupsRequest.Builder converted = ListBackupsRequest.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_TimeRangeLowerBound().is_Some()) {
      converted.timeRangeLowerBound(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_TimeRangeLowerBound().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_TimeRangeUpperBound().is_Some()) {
      converted.timeRangeUpperBound(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_TimeRangeUpperBound().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ExclusiveStartBackupArn().is_Some()) {
      converted.exclusiveStartBackupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartBackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_BackupType().is_Some()) {
      converted.backupType(ToNative.BackupTypeFilter(dafnyValue.dtor_BackupType().dtor_value()));
    }
    return converted.build();
  }

  public static ListContributorInsightsRequest ListContributorInsightsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListContributorInsightsInput dafnyValue) {
    ListContributorInsightsRequest.Builder converted = ListContributorInsightsRequest.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      converted.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_MaxResults().is_Some()) {
      converted.maxResults((dafnyValue.dtor_MaxResults().dtor_value()));
    }
    return converted.build();
  }

  public static ListExportsRequest ListExportsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListExportsInput dafnyValue) {
    ListExportsRequest.Builder converted = ListExportsRequest.builder();
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_MaxResults().is_Some()) {
      converted.maxResults((dafnyValue.dtor_MaxResults().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      converted.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return converted.build();
  }

  public static ListGlobalTablesRequest ListGlobalTablesInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListGlobalTablesInput dafnyValue) {
    ListGlobalTablesRequest.Builder converted = ListGlobalTablesRequest.builder();
    if (dafnyValue.dtor_ExclusiveStartGlobalTableName().is_Some()) {
      converted.exclusiveStartGlobalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartGlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_RegionName().is_Some()) {
      converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    return converted.build();
  }

  public static ListImportsRequest ListImportsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListImportsInput dafnyValue) {
    ListImportsRequest.Builder converted = ListImportsRequest.builder();
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_PageSize().is_Some()) {
      converted.pageSize((dafnyValue.dtor_PageSize().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      converted.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return converted.build();
  }

  public static ListTablesRequest ListTablesInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListTablesInput dafnyValue) {
    ListTablesRequest.Builder converted = ListTablesRequest.builder();
    if (dafnyValue.dtor_ExclusiveStartTableName().is_Some()) {
      converted.exclusiveStartTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartTableName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    return converted.build();
  }

  public static ListTagsOfResourceRequest ListTagsOfResourceInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ListTagsOfResourceInput dafnyValue) {
    ListTagsOfResourceRequest.Builder converted = ListTagsOfResourceRequest.builder();
    converted.resourceArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    if (dafnyValue.dtor_NextToken().is_Some()) {
      converted.nextToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return converted.build();
  }

  public static PutItemRequest PutItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.PutItemInput dafnyValue) {
    PutItemRequest.Builder converted = PutItemRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    if (dafnyValue.dtor_Expected().is_Some()) {
      converted.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      converted.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      converted.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      converted.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    return converted.build();
  }

  public static QueryRequest QueryInput(Dafny.Com.Amazonaws.Dynamodb.Types.QueryInput dafnyValue) {
    QueryRequest.Builder converted = QueryRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_Select().is_Some()) {
      converted.select(ToNative.Select(dafnyValue.dtor_Select().dtor_value()));
    }
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      converted.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_KeyConditions().is_Some()) {
      converted.keyConditions(ToNative.KeyConditions(dafnyValue.dtor_KeyConditions().dtor_value()));
    }
    if (dafnyValue.dtor_QueryFilter().is_Some()) {
      converted.queryFilter(ToNative.FilterConditionMap(dafnyValue.dtor_QueryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      converted.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ScanIndexForward().is_Some()) {
      converted.scanIndexForward((dafnyValue.dtor_ScanIndexForward().dtor_value()));
    }
    if (dafnyValue.dtor_ExclusiveStartKey().is_Some()) {
      converted.exclusiveStartKey(ToNative.Key(dafnyValue.dtor_ExclusiveStartKey().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      converted.projectionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_FilterExpression().is_Some()) {
      converted.filterExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FilterExpression().dtor_value()));
    }
    if (dafnyValue.dtor_KeyConditionExpression().is_Some()) {
      converted.keyConditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    return converted.build();
  }

  public static RestoreTableFromBackupRequest RestoreTableFromBackupInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.RestoreTableFromBackupInput dafnyValue) {
    RestoreTableFromBackupRequest.Builder converted = RestoreTableFromBackupRequest.builder();
    converted.targetTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetTableName()));
    converted.backupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    if (dafnyValue.dtor_BillingModeOverride().is_Some()) {
      converted.billingModeOverride(ToNative.BillingMode(dafnyValue.dtor_BillingModeOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexOverride().is_Some()) {
      converted.globalSecondaryIndexOverride(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexOverride().is_Some()) {
      converted.localSecondaryIndexOverride(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecificationOverride().is_Some()) {
      converted.sseSpecificationOverride(ToNative.SSESpecification(dafnyValue.dtor_SSESpecificationOverride().dtor_value()));
    }
    return converted.build();
  }

  public static RestoreTableToPointInTimeRequest RestoreTableToPointInTimeInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.RestoreTableToPointInTimeInput dafnyValue) {
    RestoreTableToPointInTimeRequest.Builder converted = RestoreTableToPointInTimeRequest.builder();
    if (dafnyValue.dtor_SourceTableArn().is_Some()) {
      converted.sourceTableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableArn().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableName().is_Some()) {
      converted.sourceTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableName().dtor_value()));
    }
    converted.targetTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetTableName()));
    if (dafnyValue.dtor_UseLatestRestorableTime().is_Some()) {
      converted.useLatestRestorableTime((dafnyValue.dtor_UseLatestRestorableTime().dtor_value()));
    }
    if (dafnyValue.dtor_RestoreDateTime().is_Some()) {
      converted.restoreDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_RestoreDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_BillingModeOverride().is_Some()) {
      converted.billingModeOverride(ToNative.BillingMode(dafnyValue.dtor_BillingModeOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexOverride().is_Some()) {
      converted.globalSecondaryIndexOverride(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexOverride().is_Some()) {
      converted.localSecondaryIndexOverride(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecificationOverride().is_Some()) {
      converted.sseSpecificationOverride(ToNative.SSESpecification(dafnyValue.dtor_SSESpecificationOverride().dtor_value()));
    }
    return converted.build();
  }

  public static ScanRequest ScanInput(Dafny.Com.Amazonaws.Dynamodb.Types.ScanInput dafnyValue) {
    ScanRequest.Builder converted = ScanRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      converted.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      converted.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_Select().is_Some()) {
      converted.select(ToNative.Select(dafnyValue.dtor_Select().dtor_value()));
    }
    if (dafnyValue.dtor_ScanFilter().is_Some()) {
      converted.scanFilter(ToNative.FilterConditionMap(dafnyValue.dtor_ScanFilter().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      converted.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ExclusiveStartKey().is_Some()) {
      converted.exclusiveStartKey(ToNative.Key(dafnyValue.dtor_ExclusiveStartKey().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_TotalSegments().is_Some()) {
      converted.totalSegments((dafnyValue.dtor_TotalSegments().dtor_value()));
    }
    if (dafnyValue.dtor_Segment().is_Some()) {
      converted.segment((dafnyValue.dtor_Segment().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      converted.projectionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_FilterExpression().is_Some()) {
      converted.filterExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FilterExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    return converted.build();
  }

  public static TagResourceRequest TagResourceInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.TagResourceInput dafnyValue) {
    TagResourceRequest.Builder converted = TagResourceRequest.builder();
    converted.resourceArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    converted.tags(ToNative.TagList(dafnyValue.dtor_Tags()));
    return converted.build();
  }

  public static TransactGetItemsRequest TransactGetItemsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.TransactGetItemsInput dafnyValue) {
    TransactGetItemsRequest.Builder converted = TransactGetItemsRequest.builder();
    converted.transactItems(ToNative.TransactGetItemList(dafnyValue.dtor_TransactItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    return converted.build();
  }

  public static TransactWriteItemsRequest TransactWriteItemsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.TransactWriteItemsInput dafnyValue) {
    TransactWriteItemsRequest.Builder converted = TransactWriteItemsRequest.builder();
    converted.transactItems(ToNative.TransactWriteItemList(dafnyValue.dtor_TransactItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      converted.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ClientRequestToken().is_Some()) {
      converted.clientRequestToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientRequestToken().dtor_value()));
    }
    return converted.build();
  }

  public static UntagResourceRequest UntagResourceInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UntagResourceInput dafnyValue) {
    UntagResourceRequest.Builder converted = UntagResourceRequest.builder();
    converted.resourceArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    converted.tagKeys(ToNative.TagKeyList(dafnyValue.dtor_TagKeys()));
    return converted.build();
  }

  public static UpdateContinuousBackupsRequest UpdateContinuousBackupsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateContinuousBackupsInput dafnyValue) {
    UpdateContinuousBackupsRequest.Builder converted = UpdateContinuousBackupsRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.pointInTimeRecoverySpecification(ToNative.PointInTimeRecoverySpecification(dafnyValue.dtor_PointInTimeRecoverySpecification()));
    return converted.build();
  }

  public static UpdateContributorInsightsRequest UpdateContributorInsightsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateContributorInsightsInput dafnyValue) {
    UpdateContributorInsightsRequest.Builder converted = UpdateContributorInsightsRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    converted.contributorInsightsAction(ToNative.ContributorInsightsAction(dafnyValue.dtor_ContributorInsightsAction()));
    return converted.build();
  }

  public static UpdateGlobalTableRequest UpdateGlobalTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateGlobalTableInput dafnyValue) {
    UpdateGlobalTableRequest.Builder converted = UpdateGlobalTableRequest.builder();
    converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    converted.replicaUpdates(ToNative.ReplicaUpdateList(dafnyValue.dtor_ReplicaUpdates()));
    return converted.build();
  }

  public static UpdateGlobalTableSettingsRequest UpdateGlobalTableSettingsInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateGlobalTableSettingsInput dafnyValue) {
    UpdateGlobalTableSettingsRequest.Builder converted = UpdateGlobalTableSettingsRequest.builder();
    converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    if (dafnyValue.dtor_GlobalTableBillingMode().is_Some()) {
      converted.globalTableBillingMode(ToNative.BillingMode(dafnyValue.dtor_GlobalTableBillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableProvisionedWriteCapacityUnits().is_Some()) {
      converted.globalTableProvisionedWriteCapacityUnits((dafnyValue.dtor_GlobalTableProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate().is_Some()) {
      converted.globalTableProvisionedWriteCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableGlobalSecondaryIndexSettingsUpdate().is_Some()) {
      converted.globalTableGlobalSecondaryIndexSettingsUpdate(ToNative.GlobalTableGlobalSecondaryIndexSettingsUpdateList(dafnyValue.dtor_GlobalTableGlobalSecondaryIndexSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettingsUpdate().is_Some()) {
      converted.replicaSettingsUpdate(ToNative.ReplicaSettingsUpdateList(dafnyValue.dtor_ReplicaSettingsUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static UpdateItemRequest UpdateItemInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateItemInput dafnyValue) {
    UpdateItemRequest.Builder converted = UpdateItemRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_AttributeUpdates().is_Some()) {
      converted.attributeUpdates(ToNative.AttributeUpdates(dafnyValue.dtor_AttributeUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_Expected().is_Some()) {
      converted.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      converted.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      converted.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      converted.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      converted.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_UpdateExpression().is_Some()) {
      converted.updateExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_UpdateExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    return converted.build();
  }

  public static UpdateTableRequest UpdateTableInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTableInput dafnyValue) {
    UpdateTableRequest.Builder converted = UpdateTableRequest.builder();
    if (dafnyValue.dtor_AttributeDefinitions().is_Some()) {
      converted.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions().dtor_value()));
    }
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      converted.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexUpdates().is_Some()) {
      converted.globalSecondaryIndexUpdates(ToNative.GlobalSecondaryIndexUpdateList(dafnyValue.dtor_GlobalSecondaryIndexUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      converted.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      converted.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaUpdates().is_Some()) {
      converted.replicaUpdates(ToNative.ReplicationGroupUpdateList(dafnyValue.dtor_ReplicaUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_TableClass().is_Some()) {
      converted.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    return converted.build();
  }

  public static UpdateTableReplicaAutoScalingRequest UpdateTableReplicaAutoScalingInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTableReplicaAutoScalingInput dafnyValue) {
    UpdateTableReplicaAutoScalingRequest.Builder converted = UpdateTableReplicaAutoScalingRequest.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexUpdates().is_Some()) {
      converted.globalSecondaryIndexUpdates(ToNative.GlobalSecondaryIndexAutoScalingUpdateList(dafnyValue.dtor_GlobalSecondaryIndexUpdates().dtor_value()));
    }
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().is_Some()) {
      converted.provisionedWriteCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaUpdates().is_Some()) {
      converted.replicaUpdates(ToNative.ReplicaAutoScalingUpdateList(dafnyValue.dtor_ReplicaUpdates().dtor_value()));
    }
    return converted.build();
  }

  public static UpdateTimeToLiveRequest UpdateTimeToLiveInput(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateTimeToLiveInput dafnyValue) {
    UpdateTimeToLiveRequest.Builder converted = UpdateTimeToLiveRequest.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.timeToLiveSpecification(ToNative.TimeToLiveSpecification(dafnyValue.dtor_TimeToLiveSpecification()));
    return converted.build();
  }

  public static List<BatchStatementRequest> PartiQLBatchRequest(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementRequest> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::BatchStatementRequest);
  }

  public static ReturnConsumedCapacity ReturnConsumedCapacity(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReturnConsumedCapacity dafnyValue) {
    if (dafnyValue.is_INDEXES()) {
      return ReturnConsumedCapacity.INDEXES;
    }
    if (dafnyValue.is_TOTAL()) {
      return ReturnConsumedCapacity.TOTAL;
    }
    if (dafnyValue.is_NONE()) {
      return ReturnConsumedCapacity.NONE;
    }
    return ReturnConsumedCapacity.fromValue(dafnyValue.toString());
  }

  public static Map<String, KeysAndAttributes> BatchGetRequestMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.KeysAndAttributes> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::KeysAndAttributes);
  }

  public static Map<String, List<WriteRequest>> BatchWriteItemRequestMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.WriteRequest>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::WriteRequests);
  }

  public static ReturnItemCollectionMetrics ReturnItemCollectionMetrics(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReturnItemCollectionMetrics dafnyValue) {
    if (dafnyValue.is_SIZE()) {
      return ReturnItemCollectionMetrics.SIZE;
    }
    if (dafnyValue.is_NONE()) {
      return ReturnItemCollectionMetrics.NONE;
    }
    return ReturnItemCollectionMetrics.fromValue(dafnyValue.toString());
  }

  public static List<Replica> ReplicaList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.Replica> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Replica);
  }

  public static List<AttributeDefinition> AttributeDefinitions(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeDefinition> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeDefinition);
  }

  public static List<KeySchemaElement> KeySchema(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.KeySchemaElement> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::KeySchemaElement);
  }

  public static List<LocalSecondaryIndex> LocalSecondaryIndexList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndex> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::LocalSecondaryIndex);
  }

  public static List<GlobalSecondaryIndex> GlobalSecondaryIndexList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndex> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalSecondaryIndex);
  }

  public static BillingMode BillingMode(Dafny.Com.Amazonaws.Dynamodb.Types.BillingMode dafnyValue) {
    if (dafnyValue.is_PROVISIONED()) {
      return BillingMode.PROVISIONED;
    }
    if (dafnyValue.is_PAY__PER__REQUEST()) {
      return BillingMode.PAY_PER_REQUEST;
    }
    return BillingMode.fromValue(dafnyValue.toString());
  }

  public static ProvisionedThroughput ProvisionedThroughput(
      Dafny.Com.Amazonaws.Dynamodb.Types.ProvisionedThroughput dafnyValue) {
    ProvisionedThroughput.Builder converted = ProvisionedThroughput.builder();
    converted.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits()));
    converted.writeCapacityUnits((dafnyValue.dtor_WriteCapacityUnits()));
    return converted.build();
  }

  public static StreamSpecification StreamSpecification(
      Dafny.Com.Amazonaws.Dynamodb.Types.StreamSpecification dafnyValue) {
    StreamSpecification.Builder converted = StreamSpecification.builder();
    converted.streamEnabled((dafnyValue.dtor_StreamEnabled()));
    if (dafnyValue.dtor_StreamViewType().is_Some()) {
      converted.streamViewType(ToNative.StreamViewType(dafnyValue.dtor_StreamViewType().dtor_value()));
    }
    return converted.build();
  }

  public static SSESpecification SSESpecification(
      Dafny.Com.Amazonaws.Dynamodb.Types.SSESpecification dafnyValue) {
    SSESpecification.Builder converted = SSESpecification.builder();
    if (dafnyValue.dtor_Enabled().is_Some()) {
      converted.enabled((dafnyValue.dtor_Enabled().dtor_value()));
    }
    if (dafnyValue.dtor_SSEType().is_Some()) {
      converted.sseType(ToNative.SSEType(dafnyValue.dtor_SSEType().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      converted.kmsMasterKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    return converted.build();
  }

  public static List<Tag> TagList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.Tag> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Tag);
  }

  public static TableClass TableClass(Dafny.Com.Amazonaws.Dynamodb.Types.TableClass dafnyValue) {
    if (dafnyValue.is_STANDARD()) {
      return TableClass.STANDARD;
    }
    if (dafnyValue.is_STANDARD__INFREQUENT__ACCESS()) {
      return TableClass.STANDARD_INFREQUENT_ACCESS;
    }
    return TableClass.fromValue(dafnyValue.toString());
  }

  public static Map<String, AttributeValue> Key(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static Map<String, ExpectedAttributeValue> ExpectedAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.ExpectedAttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ExpectedAttributeValue);
  }

  public static Map<String, AttributeValue> AttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }
  public static ConditionalOperator ConditionalOperator(
      Dafny.Com.Amazonaws.Dynamodb.Types.ConditionalOperator dafnyValue) {
    if (dafnyValue.is_AND()) {
      return ConditionalOperator.AND;
    }
    if (dafnyValue.is_OR()) {
      return ConditionalOperator.OR;
    }
    return ConditionalOperator.fromValue(dafnyValue.toString());
  }

  public static ReturnValue ReturnValue(Dafny.Com.Amazonaws.Dynamodb.Types.ReturnValue dafnyValue) {
    if (dafnyValue.is_NONE()) {
      return ReturnValue.NONE;
    }
    if (dafnyValue.is_ALL__OLD()) {
      return ReturnValue.ALL_OLD;
    }
    if (dafnyValue.is_UPDATED__OLD()) {
      return ReturnValue.UPDATED_OLD;
    }
    if (dafnyValue.is_ALL__NEW()) {
      return ReturnValue.ALL_NEW;
    }
    if (dafnyValue.is_UPDATED__NEW()) {
      return ReturnValue.UPDATED_NEW;
    }
    return ReturnValue.fromValue(dafnyValue.toString());
  }

  public static Map<String, String> ExpressionAttributeNameMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static Map<String, AttributeValue> ExpressionAttributeValueMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static List<AttributeValue> PreparedStatementParameters(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static List<ParameterizedStatement> ParameterizedStatements(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ParameterizedStatement> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ParameterizedStatement);
  }

  public static S3SseAlgorithm S3SseAlgorithm(
      Dafny.Com.Amazonaws.Dynamodb.Types.S3SseAlgorithm dafnyValue) {
    if (dafnyValue.is_AES256()) {
      return S3SseAlgorithm.AES256;
    }
    if (dafnyValue.is_KMS()) {
      return S3SseAlgorithm.KMS;
    }
    return S3SseAlgorithm.fromValue(dafnyValue.toString());
  }

  public static ExportFormat ExportFormat(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportFormat dafnyValue) {
    if (dafnyValue.is_DYNAMODB__JSON()) {
      return ExportFormat.DYNAMODB_JSON;
    }
    if (dafnyValue.is_ION()) {
      return ExportFormat.ION;
    }
    return ExportFormat.fromValue(dafnyValue.toString());
  }

  public static List<String> AttributeNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static S3BucketSource S3BucketSource(
      Dafny.Com.Amazonaws.Dynamodb.Types.S3BucketSource dafnyValue) {
    S3BucketSource.Builder converted = S3BucketSource.builder();
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      converted.s3BucketOwner(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    converted.s3Bucket(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket()));
    if (dafnyValue.dtor_S3KeyPrefix().is_Some()) {
      converted.s3KeyPrefix(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3KeyPrefix().dtor_value()));
    }
    return converted.build();
  }

  public static InputFormat InputFormat(Dafny.Com.Amazonaws.Dynamodb.Types.InputFormat dafnyValue) {
    if (dafnyValue.is_DYNAMODB__JSON()) {
      return InputFormat.DYNAMODB_JSON;
    }
    if (dafnyValue.is_ION()) {
      return InputFormat.ION;
    }
    if (dafnyValue.is_CSV()) {
      return InputFormat.CSV;
    }
    return InputFormat.fromValue(dafnyValue.toString());
  }

  public static InputFormatOptions InputFormatOptions(
      Dafny.Com.Amazonaws.Dynamodb.Types.InputFormatOptions dafnyValue) {
    InputFormatOptions.Builder converted = InputFormatOptions.builder();
    if (dafnyValue.dtor_Csv().is_Some()) {
      converted.csv(ToNative.CsvOptions(dafnyValue.dtor_Csv().dtor_value()));
    }
    return converted.build();
  }

  public static InputCompressionType InputCompressionType(
      Dafny.Com.Amazonaws.Dynamodb.Types.InputCompressionType dafnyValue) {
    if (dafnyValue.is_GZIP()) {
      return InputCompressionType.GZIP;
    }
    if (dafnyValue.is_ZSTD()) {
      return InputCompressionType.ZSTD;
    }
    if (dafnyValue.is_NONE()) {
      return InputCompressionType.NONE;
    }
    return InputCompressionType.fromValue(dafnyValue.toString());
  }

  public static TableCreationParameters TableCreationParameters(
      Dafny.Com.Amazonaws.Dynamodb.Types.TableCreationParameters dafnyValue) {
    TableCreationParameters.Builder converted = TableCreationParameters.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions()));
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      converted.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      converted.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    return converted.build();
  }

  public static BackupTypeFilter BackupTypeFilter(
      Dafny.Com.Amazonaws.Dynamodb.Types.BackupTypeFilter dafnyValue) {
    if (dafnyValue.is_USER()) {
      return BackupTypeFilter.USER;
    }
    if (dafnyValue.is_SYSTEM()) {
      return BackupTypeFilter.SYSTEM;
    }
    if (dafnyValue.is_AWS__BACKUP()) {
      return BackupTypeFilter.AWS_BACKUP;
    }
    if (dafnyValue.is_ALL()) {
      return BackupTypeFilter.ALL;
    }
    return BackupTypeFilter.fromValue(dafnyValue.toString());
  }

  public static Map<String, AttributeValue> PutItemInputAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static Select Select(Dafny.Com.Amazonaws.Dynamodb.Types.Select dafnyValue) {
    if (dafnyValue.is_ALL__ATTRIBUTES()) {
      return Select.ALL_ATTRIBUTES;
    }
    if (dafnyValue.is_ALL__PROJECTED__ATTRIBUTES()) {
      return Select.ALL_PROJECTED_ATTRIBUTES;
    }
    if (dafnyValue.is_SPECIFIC__ATTRIBUTES()) {
      return Select.SPECIFIC_ATTRIBUTES;
    }
    if (dafnyValue.is_COUNT()) {
      return Select.COUNT;
    }
    return Select.fromValue(dafnyValue.toString());
  }

  public static Map<String, Condition> KeyConditions(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.Condition> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Condition);
  }

  public static Map<String, Condition> FilterConditionMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.Condition> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Condition);
  }

  public static List<TransactGetItem> TransactGetItemList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.TransactGetItem> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::TransactGetItem);
  }

  public static List<TransactWriteItem> TransactWriteItemList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.TransactWriteItem> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::TransactWriteItem);
  }

  public static List<String> TagKeyList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static PointInTimeRecoverySpecification PointInTimeRecoverySpecification(
      Dafny.Com.Amazonaws.Dynamodb.Types.PointInTimeRecoverySpecification dafnyValue) {
    PointInTimeRecoverySpecification.Builder converted = PointInTimeRecoverySpecification.builder();
    converted.pointInTimeRecoveryEnabled((dafnyValue.dtor_PointInTimeRecoveryEnabled()));
    return converted.build();
  }

  public static ContributorInsightsAction ContributorInsightsAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.ContributorInsightsAction dafnyValue) {
    if (dafnyValue.is_ENABLE()) {
      return ContributorInsightsAction.ENABLE;
    }
    if (dafnyValue.is_DISABLE()) {
      return ContributorInsightsAction.DISABLE;
    }
    return ContributorInsightsAction.fromValue(dafnyValue.toString());
  }

  public static List<ReplicaUpdate> ReplicaUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaUpdate);
  }

  public static AutoScalingSettingsUpdate AutoScalingSettingsUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingSettingsUpdate dafnyValue) {
    AutoScalingSettingsUpdate.Builder converted = AutoScalingSettingsUpdate.builder();
    if (dafnyValue.dtor_MinimumUnits().is_Some()) {
      converted.minimumUnits((dafnyValue.dtor_MinimumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_MaximumUnits().is_Some()) {
      converted.maximumUnits((dafnyValue.dtor_MaximumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingDisabled().is_Some()) {
      converted.autoScalingDisabled((dafnyValue.dtor_AutoScalingDisabled().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingRoleArn().is_Some()) {
      converted.autoScalingRoleArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AutoScalingRoleArn().dtor_value()));
    }
    if (dafnyValue.dtor_ScalingPolicyUpdate().is_Some()) {
      converted.scalingPolicyUpdate(ToNative.AutoScalingPolicyUpdate(dafnyValue.dtor_ScalingPolicyUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static List<GlobalTableGlobalSecondaryIndexSettingsUpdate> GlobalTableGlobalSecondaryIndexSettingsUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTableGlobalSecondaryIndexSettingsUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalTableGlobalSecondaryIndexSettingsUpdate);
  }

  public static List<ReplicaSettingsUpdate> ReplicaSettingsUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaSettingsUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaSettingsUpdate);
  }

  public static Map<String, AttributeValueUpdate> AttributeUpdates(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValueUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValueUpdate);
  }

  public static List<GlobalSecondaryIndexUpdate> GlobalSecondaryIndexUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalSecondaryIndexUpdate);
  }

  public static List<ReplicationGroupUpdate> ReplicationGroupUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicationGroupUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicationGroupUpdate);
  }

  public static List<GlobalSecondaryIndexAutoScalingUpdate> GlobalSecondaryIndexAutoScalingUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexAutoScalingUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalSecondaryIndexAutoScalingUpdate);
  }

  public static List<ReplicaAutoScalingUpdate> ReplicaAutoScalingUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaAutoScalingUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaAutoScalingUpdate);
  }

  public static TimeToLiveSpecification TimeToLiveSpecification(
      Dafny.Com.Amazonaws.Dynamodb.Types.TimeToLiveSpecification dafnyValue) {
    TimeToLiveSpecification.Builder converted = TimeToLiveSpecification.builder();
    converted.enabled((dafnyValue.dtor_Enabled()));
    converted.attributeName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    return converted.build();
  }

  public static List<BatchStatementResponse> PartiQLBatchResponse(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementResponse> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::BatchStatementResponse);
  }

  public static List<ConsumedCapacity> ConsumedCapacityMultiple(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ConsumedCapacity> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ConsumedCapacity);
  }

  public static Map<String, List<Map<String, AttributeValue>>> BatchGetResponseMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue>>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ItemList);
  }

  public static Map<String, List<ItemCollectionMetrics>> ItemCollectionMetricsPerTable(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ItemCollectionMetrics>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ItemCollectionMetricsMultiple);
  }

  public static BackupDetails BackupDetails(
      Dafny.Com.Amazonaws.Dynamodb.Types.BackupDetails dafnyValue) {
    BackupDetails.Builder converted = BackupDetails.builder();
    converted.backupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    converted.backupName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName()));
    if (dafnyValue.dtor_BackupSizeBytes().is_Some()) {
      converted.backupSizeBytes((dafnyValue.dtor_BackupSizeBytes().dtor_value()));
    }
    converted.backupStatus(ToNative.BackupStatus(dafnyValue.dtor_BackupStatus()));
    converted.backupType(ToNative.BackupType(dafnyValue.dtor_BackupType()));
    converted.backupCreationDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_BackupCreationDateTime()).toInstant());
    if (dafnyValue.dtor_BackupExpiryDateTime().is_Some()) {
      converted.backupExpiryDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_BackupExpiryDateTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static GlobalTableDescription GlobalTableDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTableDescription dafnyValue) {
    GlobalTableDescription.Builder converted = GlobalTableDescription.builder();
    if (dafnyValue.dtor_ReplicationGroup().is_Some()) {
      converted.replicationGroup(ToNative.ReplicaDescriptionList(dafnyValue.dtor_ReplicationGroup().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableArn().is_Some()) {
      converted.globalTableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableArn().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDateTime().is_Some()) {
      converted.creationDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_CreationDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_GlobalTableStatus().is_Some()) {
      converted.globalTableStatus(ToNative.GlobalTableStatus(dafnyValue.dtor_GlobalTableStatus().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    return converted.build();
  }

  public static TableDescription TableDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.TableDescription dafnyValue) {
    TableDescription.Builder converted = TableDescription.builder();
    if (dafnyValue.dtor_AttributeDefinitions().is_Some()) {
      converted.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_TableStatus().is_Some()) {
      converted.tableStatus(ToNative.TableStatus(dafnyValue.dtor_TableStatus().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDateTime().is_Some()) {
      converted.creationDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_CreationDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughputDescription(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_TableSizeBytes().is_Some()) {
      converted.tableSizeBytes((dafnyValue.dtor_TableSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      converted.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      converted.tableId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_BillingModeSummary().is_Some()) {
      converted.billingModeSummary(ToNative.BillingModeSummary(dafnyValue.dtor_BillingModeSummary().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      converted.localSecondaryIndexes(ToNative.LocalSecondaryIndexDescriptionList(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      converted.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_LatestStreamLabel().is_Some()) {
      converted.latestStreamLabel(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LatestStreamLabel().dtor_value()));
    }
    if (dafnyValue.dtor_LatestStreamArn().is_Some()) {
      converted.latestStreamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LatestStreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableVersion().is_Some()) {
      converted.globalTableVersion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableVersion().dtor_value()));
    }
    if (dafnyValue.dtor_Replicas().is_Some()) {
      converted.replicas(ToNative.ReplicaDescriptionList(dafnyValue.dtor_Replicas().dtor_value()));
    }
    if (dafnyValue.dtor_RestoreSummary().is_Some()) {
      converted.restoreSummary(ToNative.RestoreSummary(dafnyValue.dtor_RestoreSummary().dtor_value()));
    }
    if (dafnyValue.dtor_SSEDescription().is_Some()) {
      converted.sseDescription(ToNative.SSEDescription(dafnyValue.dtor_SSEDescription().dtor_value()));
    }
    if (dafnyValue.dtor_ArchivalSummary().is_Some()) {
      converted.archivalSummary(ToNative.ArchivalSummary(dafnyValue.dtor_ArchivalSummary().dtor_value()));
    }
    if (dafnyValue.dtor_TableClassSummary().is_Some()) {
      converted.tableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_TableClassSummary().dtor_value()));
    }
    return converted.build();
  }

  public static BackupDescription BackupDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.BackupDescription dafnyValue) {
    BackupDescription.Builder converted = BackupDescription.builder();
    if (dafnyValue.dtor_BackupDetails().is_Some()) {
      converted.backupDetails(ToNative.BackupDetails(dafnyValue.dtor_BackupDetails().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableDetails().is_Some()) {
      converted.sourceTableDetails(ToNative.SourceTableDetails(dafnyValue.dtor_SourceTableDetails().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableFeatureDetails().is_Some()) {
      converted.sourceTableFeatureDetails(ToNative.SourceTableFeatureDetails(dafnyValue.dtor_SourceTableFeatureDetails().dtor_value()));
    }
    return converted.build();
  }

  public static ConsumedCapacity ConsumedCapacity(
      Dafny.Com.Amazonaws.Dynamodb.Types.ConsumedCapacity dafnyValue) {
    ConsumedCapacity.Builder converted = ConsumedCapacity.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_CapacityUnits().is_Some()) {
      converted.capacityUnits(Double.valueOf(dafnyValue.dtor_CapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      converted.readCapacityUnits(Double.valueOf(dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      converted.writeCapacityUnits(Double.valueOf(dafnyValue.dtor_WriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_Table().is_Some()) {
      converted.table(ToNative.Capacity(dafnyValue.dtor_Table().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      converted.localSecondaryIndexes(ToNative.SecondaryIndexesCapacityMap(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.SecondaryIndexesCapacityMap(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    return converted.build();
  }

  public static ItemCollectionMetrics ItemCollectionMetrics(
      Dafny.Com.Amazonaws.Dynamodb.Types.ItemCollectionMetrics dafnyValue) {
    ItemCollectionMetrics.Builder converted = ItemCollectionMetrics.builder();
    if (dafnyValue.dtor_ItemCollectionKey().is_Some()) {
      converted.itemCollectionKey(ToNative.ItemCollectionKeyAttributeMap(dafnyValue.dtor_ItemCollectionKey().dtor_value()));
    }
    if (dafnyValue.dtor_SizeEstimateRangeGB().is_Some()) {
      converted.sizeEstimateRangeGB(ToNative.ItemCollectionSizeEstimateRange(dafnyValue.dtor_SizeEstimateRangeGB().dtor_value()));
    }
    return converted.build();
  }

  public static ContinuousBackupsDescription ContinuousBackupsDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ContinuousBackupsDescription dafnyValue) {
    ContinuousBackupsDescription.Builder converted = ContinuousBackupsDescription.builder();
    converted.continuousBackupsStatus(ToNative.ContinuousBackupsStatus(dafnyValue.dtor_ContinuousBackupsStatus()));
    if (dafnyValue.dtor_PointInTimeRecoveryDescription().is_Some()) {
      converted.pointInTimeRecoveryDescription(ToNative.PointInTimeRecoveryDescription(dafnyValue.dtor_PointInTimeRecoveryDescription().dtor_value()));
    }
    return converted.build();
  }

  public static List<String> ContributorInsightsRuleList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static ContributorInsightsStatus ContributorInsightsStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.ContributorInsightsStatus dafnyValue) {
    if (dafnyValue.is_ENABLING()) {
      return ContributorInsightsStatus.ENABLING;
    }
    if (dafnyValue.is_ENABLED()) {
      return ContributorInsightsStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLING()) {
      return ContributorInsightsStatus.DISABLING;
    }
    if (dafnyValue.is_DISABLED()) {
      return ContributorInsightsStatus.DISABLED;
    }
    if (dafnyValue.is_FAILED()) {
      return ContributorInsightsStatus.FAILED;
    }
    return ContributorInsightsStatus.fromValue(dafnyValue.toString());
  }

  public static FailureException FailureException(
      Dafny.Com.Amazonaws.Dynamodb.Types.FailureException dafnyValue) {
    FailureException.Builder converted = FailureException.builder();
    if (dafnyValue.dtor_ExceptionName().is_Some()) {
      converted.exceptionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExceptionName().dtor_value()));
    }
    if (dafnyValue.dtor_ExceptionDescription().is_Some()) {
      converted.exceptionDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExceptionDescription().dtor_value()));
    }
    return converted.build();
  }

  public static List<Endpoint> Endpoints(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.Endpoint> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Endpoint);
  }

  public static ExportDescription ExportDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportDescription dafnyValue) {
    ExportDescription.Builder converted = ExportDescription.builder();
    if (dafnyValue.dtor_ExportArn().is_Some()) {
      converted.exportArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ExportStatus().is_Some()) {
      converted.exportStatus(ToNative.ExportStatus(dafnyValue.dtor_ExportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      converted.startTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_StartTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      converted.endTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_EndTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ExportManifest().is_Some()) {
      converted.exportManifest(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportManifest().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      converted.tableId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_ExportTime().is_Some()) {
      converted.exportTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_ExportTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      converted.clientToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_S3Bucket().is_Some()) {
      converted.s3Bucket(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      converted.s3BucketOwner(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    if (dafnyValue.dtor_S3Prefix().is_Some()) {
      converted.s3Prefix(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Prefix().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseAlgorithm().is_Some()) {
      converted.s3SseAlgorithm(ToNative.S3SseAlgorithm(dafnyValue.dtor_S3SseAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseKmsKeyId().is_Some()) {
      converted.s3SseKmsKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3SseKmsKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_FailureCode().is_Some()) {
      converted.failureCode(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureCode().dtor_value()));
    }
    if (dafnyValue.dtor_FailureMessage().is_Some()) {
      converted.failureMessage(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureMessage().dtor_value()));
    }
    if (dafnyValue.dtor_ExportFormat().is_Some()) {
      converted.exportFormat(ToNative.ExportFormat(dafnyValue.dtor_ExportFormat().dtor_value()));
    }
    if (dafnyValue.dtor_BilledSizeBytes().is_Some()) {
      converted.billedSizeBytes((dafnyValue.dtor_BilledSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      converted.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    return converted.build();
  }

  public static List<ReplicaSettingsDescription> ReplicaSettingsDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaSettingsDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaSettingsDescription);
  }

  public static ImportTableDescription ImportTableDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ImportTableDescription dafnyValue) {
    ImportTableDescription.Builder converted = ImportTableDescription.builder();
    if (dafnyValue.dtor_ImportArn().is_Some()) {
      converted.importArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ImportStatus().is_Some()) {
      converted.importStatus(ToNative.ImportStatus(dafnyValue.dtor_ImportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      converted.tableId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      converted.clientToken(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketSource().is_Some()) {
      converted.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource().dtor_value()));
    }
    if (dafnyValue.dtor_ErrorCount().is_Some()) {
      converted.errorCount((dafnyValue.dtor_ErrorCount().dtor_value()));
    }
    if (dafnyValue.dtor_CloudWatchLogGroupArn().is_Some()) {
      converted.cloudWatchLogGroupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudWatchLogGroupArn().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormat().is_Some()) {
      converted.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormatOptions().is_Some()) {
      converted.inputFormatOptions(ToNative.InputFormatOptions(dafnyValue.dtor_InputFormatOptions().dtor_value()));
    }
    if (dafnyValue.dtor_InputCompressionType().is_Some()) {
      converted.inputCompressionType(ToNative.InputCompressionType(dafnyValue.dtor_InputCompressionType().dtor_value()));
    }
    if (dafnyValue.dtor_TableCreationParameters().is_Some()) {
      converted.tableCreationParameters(ToNative.TableCreationParameters(dafnyValue.dtor_TableCreationParameters().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      converted.startTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_StartTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      converted.endTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_EndTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ProcessedSizeBytes().is_Some()) {
      converted.processedSizeBytes((dafnyValue.dtor_ProcessedSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ProcessedItemCount().is_Some()) {
      converted.processedItemCount((dafnyValue.dtor_ProcessedItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_ImportedItemCount().is_Some()) {
      converted.importedItemCount((dafnyValue.dtor_ImportedItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_FailureCode().is_Some()) {
      converted.failureCode(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureCode().dtor_value()));
    }
    if (dafnyValue.dtor_FailureMessage().is_Some()) {
      converted.failureMessage(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureMessage().dtor_value()));
    }
    return converted.build();
  }

  public static List<KinesisDataStreamDestination> KinesisDataStreamDestinations(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.KinesisDataStreamDestination> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::KinesisDataStreamDestination);
  }

  public static TableAutoScalingDescription TableAutoScalingDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.TableAutoScalingDescription dafnyValue) {
    TableAutoScalingDescription.Builder converted = TableAutoScalingDescription.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_TableStatus().is_Some()) {
      converted.tableStatus(ToNative.TableStatus(dafnyValue.dtor_TableStatus().dtor_value()));
    }
    if (dafnyValue.dtor_Replicas().is_Some()) {
      converted.replicas(ToNative.ReplicaAutoScalingDescriptionList(dafnyValue.dtor_Replicas().dtor_value()));
    }
    return converted.build();
  }

  public static TimeToLiveDescription TimeToLiveDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.TimeToLiveDescription dafnyValue) {
    TimeToLiveDescription.Builder converted = TimeToLiveDescription.builder();
    if (dafnyValue.dtor_TimeToLiveStatus().is_Some()) {
      converted.timeToLiveStatus(ToNative.TimeToLiveStatus(dafnyValue.dtor_TimeToLiveStatus().dtor_value()));
    }
    if (dafnyValue.dtor_AttributeName().is_Some()) {
      converted.attributeName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName().dtor_value()));
    }
    return converted.build();
  }

  public static DestinationStatus DestinationStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.DestinationStatus dafnyValue) {
    if (dafnyValue.is_ENABLING()) {
      return DestinationStatus.ENABLING;
    }
    if (dafnyValue.is_ACTIVE()) {
      return DestinationStatus.ACTIVE;
    }
    if (dafnyValue.is_DISABLING()) {
      return DestinationStatus.DISABLING;
    }
    if (dafnyValue.is_DISABLED()) {
      return DestinationStatus.DISABLED;
    }
    if (dafnyValue.is_ENABLE__FAILED()) {
      return DestinationStatus.ENABLE_FAILED;
    }
    return DestinationStatus.fromValue(dafnyValue.toString());
  }

  public static List<Map<String, AttributeValue>> ItemList(
      DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeMap);
  }

  public static List<ItemResponse> ItemResponseList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ItemResponse> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ItemResponse);
  }

  public static List<BackupSummary> BackupSummaries(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.BackupSummary> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::BackupSummary);
  }

  public static List<ContributorInsightsSummary> ContributorInsightsSummaries(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ContributorInsightsSummary> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ContributorInsightsSummary);
  }

  public static List<ExportSummary> ExportSummaries(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ExportSummary> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ExportSummary);
  }

  public static List<GlobalTable> GlobalTableList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTable> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalTable);
  }

  public static List<ImportSummary> ImportSummaryList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ImportSummary> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ImportSummary);
  }

  public static List<String> TableNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static BatchStatementRequest BatchStatementRequest(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementRequest dafnyValue) {
    BatchStatementRequest.Builder converted = BatchStatementRequest.builder();
    converted.statement(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    if (dafnyValue.dtor_Parameters().is_Some()) {
      converted.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    return converted.build();
  }

  public static KeysAndAttributes KeysAndAttributes(
      Dafny.Com.Amazonaws.Dynamodb.Types.KeysAndAttributes dafnyValue) {
    KeysAndAttributes.Builder converted = KeysAndAttributes.builder();
    converted.keys(ToNative.KeyList(dafnyValue.dtor_Keys()));
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      converted.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      converted.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      converted.projectionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    return converted.build();
  }

  public static List<WriteRequest> WriteRequests(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.WriteRequest> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::WriteRequest);
  }

  public static Replica Replica(Dafny.Com.Amazonaws.Dynamodb.Types.Replica dafnyValue) {
    Replica.Builder converted = Replica.builder();
    if (dafnyValue.dtor_RegionName().is_Some()) {
      converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    return converted.build();
  }

  public static AttributeDefinition AttributeDefinition(
      Dafny.Com.Amazonaws.Dynamodb.Types.AttributeDefinition dafnyValue) {
    AttributeDefinition.Builder converted = AttributeDefinition.builder();
    converted.attributeName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    converted.attributeType(ToNative.ScalarAttributeType(dafnyValue.dtor_AttributeType()));
    return converted.build();
  }

  public static KeySchemaElement KeySchemaElement(
      Dafny.Com.Amazonaws.Dynamodb.Types.KeySchemaElement dafnyValue) {
    KeySchemaElement.Builder converted = KeySchemaElement.builder();
    converted.attributeName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    converted.keyType(ToNative.KeyType(dafnyValue.dtor_KeyType()));
    return converted.build();
  }

  public static LocalSecondaryIndex LocalSecondaryIndex(
      Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndex dafnyValue) {
    LocalSecondaryIndex.Builder converted = LocalSecondaryIndex.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    converted.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    return converted.build();
  }

  public static GlobalSecondaryIndex GlobalSecondaryIndex(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndex dafnyValue) {
    GlobalSecondaryIndex.Builder converted = GlobalSecondaryIndex.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    converted.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return converted.build();
  }

  public static StreamViewType StreamViewType(
      Dafny.Com.Amazonaws.Dynamodb.Types.StreamViewType dafnyValue) {
    if (dafnyValue.is_NEW__IMAGE()) {
      return StreamViewType.NEW_IMAGE;
    }
    if (dafnyValue.is_OLD__IMAGE()) {
      return StreamViewType.OLD_IMAGE;
    }
    if (dafnyValue.is_NEW__AND__OLD__IMAGES()) {
      return StreamViewType.NEW_AND_OLD_IMAGES;
    }
    if (dafnyValue.is_KEYS__ONLY()) {
      return StreamViewType.KEYS_ONLY;
    }
    return StreamViewType.fromValue(dafnyValue.toString());
  }

  public static SSEType SSEType(Dafny.Com.Amazonaws.Dynamodb.Types.SSEType dafnyValue) {
    if (dafnyValue.is_AES256()) {
      return SSEType.AES256;
    }
    if (dafnyValue.is_KMS()) {
      return SSEType.KMS;
    }
    return SSEType.fromValue(dafnyValue.toString());
  }

  public static Tag Tag(Dafny.Com.Amazonaws.Dynamodb.Types.Tag dafnyValue) {
    Tag.Builder converted = Tag.builder();
    converted.key(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Key()));
    converted.value(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Value()));
    return converted.build();
  }

  public static AttributeValue AttributeValue(
      Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue dafnyValue) {
    AttributeValue.Builder av = AttributeValue.builder();
    if (dafnyValue.is_S()) {
      av.s(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S()));
    }
    if (dafnyValue.is_N()) {
      av.n(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_N()));
    }
    if (dafnyValue.is_B()) {
      av.b(SdkBytes.fromByteBuffer(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_B())));
    }
    if (dafnyValue.is_SS()) {
      av.ss(ToNative.StringSetAttributeValue(dafnyValue.dtor_SS()));
    }
    if (dafnyValue.is_NS()) {
      av.ns(ToNative.NumberSetAttributeValue(dafnyValue.dtor_NS()));
    }
    if (dafnyValue.is_BS()) {
      av.bs(ToNative.BinarySetAttributeValue(dafnyValue.dtor_BS()).stream().map(val -> SdkBytes.fromByteBuffer(val)).collect(Collectors.toList()));
    }
    if (dafnyValue.is_M()) {
      av.m(ToNative.MapAttributeValue(dafnyValue.dtor_M()));
    }
    if (dafnyValue.is_L()) {
      av.l(ToNative.ListAttributeValue(dafnyValue.dtor_L()));
    }
    if (dafnyValue.is_NULL()) {
      av.nul((dafnyValue.dtor_NULL()));
    }
    if (dafnyValue.is_BOOL()) {
      av.bool((dafnyValue.dtor_BOOL()));
    }
    return av.build();
  }

  public static ExpectedAttributeValue ExpectedAttributeValue(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExpectedAttributeValue dafnyValue) {
    ExpectedAttributeValue.Builder converted = ExpectedAttributeValue.builder();
    if (dafnyValue.dtor_Value().is_Some()) {
      converted.value(ToNative.AttributeValue(dafnyValue.dtor_Value().dtor_value()));
    }
    if (dafnyValue.dtor_Exists().is_Some()) {
      converted.exists((dafnyValue.dtor_Exists().dtor_value()));
    }
    if (dafnyValue.dtor_ComparisonOperator().is_Some()) {
      converted.comparisonOperator(ToNative.ComparisonOperator(dafnyValue.dtor_ComparisonOperator().dtor_value()));
    }
    if (dafnyValue.dtor_AttributeValueList().is_Some()) {
      converted.attributeValueList(ToNative.AttributeValueList(dafnyValue.dtor_AttributeValueList().dtor_value()));
    }
    return converted.build();
  }

  public static ParameterizedStatement ParameterizedStatement(
      Dafny.Com.Amazonaws.Dynamodb.Types.ParameterizedStatement dafnyValue) {
    ParameterizedStatement.Builder converted = ParameterizedStatement.builder();
    converted.statement(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    if (dafnyValue.dtor_Parameters().is_Some()) {
      converted.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    return converted.build();
  }

  public static CsvOptions CsvOptions(Dafny.Com.Amazonaws.Dynamodb.Types.CsvOptions dafnyValue) {
    CsvOptions.Builder converted = CsvOptions.builder();
    if (dafnyValue.dtor_Delimiter().is_Some()) {
      converted.delimiter(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Delimiter().dtor_value()));
    }
    if (dafnyValue.dtor_HeaderList().is_Some()) {
      converted.headerList(ToNative.CsvHeaderList(dafnyValue.dtor_HeaderList().dtor_value()));
    }
    return converted.build();
  }

  public static Condition Condition(Dafny.Com.Amazonaws.Dynamodb.Types.Condition dafnyValue) {
    Condition.Builder converted = Condition.builder();
    if (dafnyValue.dtor_AttributeValueList().is_Some()) {
      converted.attributeValueList(ToNative.AttributeValueList(dafnyValue.dtor_AttributeValueList().dtor_value()));
    }
    converted.comparisonOperator(ToNative.ComparisonOperator(dafnyValue.dtor_ComparisonOperator()));
    return converted.build();
  }

  public static TransactGetItem TransactGetItem(
      Dafny.Com.Amazonaws.Dynamodb.Types.TransactGetItem dafnyValue) {
    TransactGetItem.Builder converted = TransactGetItem.builder();
    converted.get(ToNative.Get(dafnyValue.dtor_Get()));
    return converted.build();
  }

  public static TransactWriteItem TransactWriteItem(
      Dafny.Com.Amazonaws.Dynamodb.Types.TransactWriteItem dafnyValue) {
    TransactWriteItem.Builder converted = TransactWriteItem.builder();
    if (dafnyValue.dtor_ConditionCheck().is_Some()) {
      converted.conditionCheck(ToNative.ConditionCheck(dafnyValue.dtor_ConditionCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Put().is_Some()) {
      converted.put(ToNative.Put(dafnyValue.dtor_Put().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      converted.delete(ToNative.Delete(dafnyValue.dtor_Delete().dtor_value()));
    }
    if (dafnyValue.dtor_Update().is_Some()) {
      converted.update(ToNative.Update(dafnyValue.dtor_Update().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaUpdate ReplicaUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaUpdate dafnyValue) {
    ReplicaUpdate.Builder converted = ReplicaUpdate.builder();
    if (dafnyValue.dtor_Create().is_Some()) {
      converted.create(ToNative.CreateReplicaAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      converted.delete(ToNative.DeleteReplicaAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    return converted.build();
  }

  public static AutoScalingPolicyUpdate AutoScalingPolicyUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingPolicyUpdate dafnyValue) {
    AutoScalingPolicyUpdate.Builder converted = AutoScalingPolicyUpdate.builder();
    if (dafnyValue.dtor_PolicyName().is_Some()) {
      converted.policyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName().dtor_value()));
    }
    converted.targetTrackingScalingPolicyConfiguration(ToNative.AutoScalingTargetTrackingScalingPolicyConfigurationUpdate(dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration()));
    return converted.build();
  }

  public static GlobalTableGlobalSecondaryIndexSettingsUpdate GlobalTableGlobalSecondaryIndexSettingsUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTableGlobalSecondaryIndexSettingsUpdate dafnyValue) {
    GlobalTableGlobalSecondaryIndexSettingsUpdate.Builder converted = GlobalTableGlobalSecondaryIndexSettingsUpdate.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedWriteCapacityUnits().is_Some()) {
      converted.provisionedWriteCapacityUnits((dafnyValue.dtor_ProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettingsUpdate().is_Some()) {
      converted.provisionedWriteCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaSettingsUpdate ReplicaSettingsUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaSettingsUpdate dafnyValue) {
    ReplicaSettingsUpdate.Builder converted = ReplicaSettingsUpdate.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().is_Some()) {
      converted.replicaProvisionedReadCapacityUnits((dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate().is_Some()) {
      converted.replicaProvisionedReadCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettingsUpdate().is_Some()) {
      converted.replicaGlobalSecondaryIndexSettingsUpdate(ToNative.ReplicaGlobalSecondaryIndexSettingsUpdateList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTableClass().is_Some()) {
      converted.replicaTableClass(ToNative.TableClass(dafnyValue.dtor_ReplicaTableClass().dtor_value()));
    }
    return converted.build();
  }

  public static AttributeValueUpdate AttributeValueUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValueUpdate dafnyValue) {
    AttributeValueUpdate.Builder converted = AttributeValueUpdate.builder();
    if (dafnyValue.dtor_Value().is_Some()) {
      converted.value(ToNative.AttributeValue(dafnyValue.dtor_Value().dtor_value()));
    }
    if (dafnyValue.dtor_Action().is_Some()) {
      converted.action(ToNative.AttributeAction(dafnyValue.dtor_Action().dtor_value()));
    }
    return converted.build();
  }

  public static GlobalSecondaryIndexUpdate GlobalSecondaryIndexUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexUpdate dafnyValue) {
    GlobalSecondaryIndexUpdate.Builder converted = GlobalSecondaryIndexUpdate.builder();
    if (dafnyValue.dtor_Update().is_Some()) {
      converted.update(ToNative.UpdateGlobalSecondaryIndexAction(dafnyValue.dtor_Update().dtor_value()));
    }
    if (dafnyValue.dtor_Create().is_Some()) {
      converted.create(ToNative.CreateGlobalSecondaryIndexAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      converted.delete(ToNative.DeleteGlobalSecondaryIndexAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicationGroupUpdate ReplicationGroupUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicationGroupUpdate dafnyValue) {
    ReplicationGroupUpdate.Builder converted = ReplicationGroupUpdate.builder();
    if (dafnyValue.dtor_Create().is_Some()) {
      converted.create(ToNative.CreateReplicationGroupMemberAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Update().is_Some()) {
      converted.update(ToNative.UpdateReplicationGroupMemberAction(dafnyValue.dtor_Update().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      converted.delete(ToNative.DeleteReplicationGroupMemberAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    return converted.build();
  }

  public static GlobalSecondaryIndexAutoScalingUpdate GlobalSecondaryIndexAutoScalingUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexAutoScalingUpdate dafnyValue) {
    GlobalSecondaryIndexAutoScalingUpdate.Builder converted = GlobalSecondaryIndexAutoScalingUpdate.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().is_Some()) {
      converted.provisionedWriteCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaAutoScalingUpdate ReplicaAutoScalingUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaAutoScalingUpdate dafnyValue) {
    ReplicaAutoScalingUpdate.Builder converted = ReplicaAutoScalingUpdate.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexUpdates().is_Some()) {
      converted.replicaGlobalSecondaryIndexUpdates(ToNative.ReplicaGlobalSecondaryIndexAutoScalingUpdateList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingUpdate().is_Some()) {
      converted.replicaProvisionedReadCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static BatchStatementResponse BatchStatementResponse(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementResponse dafnyValue) {
    BatchStatementResponse.Builder converted = BatchStatementResponse.builder();
    if (dafnyValue.dtor_Error().is_Some()) {
      converted.error(ToNative.BatchStatementError(dafnyValue.dtor_Error().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_Item().is_Some()) {
      converted.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    return converted.build();
  }

  public static List<ItemCollectionMetrics> ItemCollectionMetricsMultiple(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ItemCollectionMetrics> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ItemCollectionMetrics);
  }

  public static BackupStatus BackupStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.BackupStatus dafnyValue) {
    if (dafnyValue.is_CREATING()) {
      return BackupStatus.CREATING;
    }
    if (dafnyValue.is_DELETED()) {
      return BackupStatus.DELETED;
    }
    if (dafnyValue.is_AVAILABLE()) {
      return BackupStatus.AVAILABLE;
    }
    return BackupStatus.fromValue(dafnyValue.toString());
  }

  public static BackupType BackupType(Dafny.Com.Amazonaws.Dynamodb.Types.BackupType dafnyValue) {
    if (dafnyValue.is_USER()) {
      return BackupType.USER;
    }
    if (dafnyValue.is_SYSTEM()) {
      return BackupType.SYSTEM;
    }
    if (dafnyValue.is_AWS__BACKUP()) {
      return BackupType.AWS_BACKUP;
    }
    return BackupType.fromValue(dafnyValue.toString());
  }

  public static List<ReplicaDescription> ReplicaDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaDescription);
  }

  public static GlobalTableStatus GlobalTableStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTableStatus dafnyValue) {
    if (dafnyValue.is_CREATING()) {
      return GlobalTableStatus.CREATING;
    }
    if (dafnyValue.is_ACTIVE()) {
      return GlobalTableStatus.ACTIVE;
    }
    if (dafnyValue.is_DELETING()) {
      return GlobalTableStatus.DELETING;
    }
    if (dafnyValue.is_UPDATING()) {
      return GlobalTableStatus.UPDATING;
    }
    return GlobalTableStatus.fromValue(dafnyValue.toString());
  }

  public static TableStatus TableStatus(Dafny.Com.Amazonaws.Dynamodb.Types.TableStatus dafnyValue) {
    if (dafnyValue.is_CREATING()) {
      return TableStatus.CREATING;
    }
    if (dafnyValue.is_UPDATING()) {
      return TableStatus.UPDATING;
    }
    if (dafnyValue.is_DELETING()) {
      return TableStatus.DELETING;
    }
    if (dafnyValue.is_ACTIVE()) {
      return TableStatus.ACTIVE;
    }
    if (dafnyValue.is_INACCESSIBLE__ENCRYPTION__CREDENTIALS()) {
      return TableStatus.INACCESSIBLE_ENCRYPTION_CREDENTIALS;
    }
    if (dafnyValue.is_ARCHIVING()) {
      return TableStatus.ARCHIVING;
    }
    if (dafnyValue.is_ARCHIVED()) {
      return TableStatus.ARCHIVED;
    }
    return TableStatus.fromValue(dafnyValue.toString());
  }

  public static ProvisionedThroughputDescription ProvisionedThroughputDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ProvisionedThroughputDescription dafnyValue) {
    ProvisionedThroughputDescription.Builder converted = ProvisionedThroughputDescription.builder();
    if (dafnyValue.dtor_LastIncreaseDateTime().is_Some()) {
      converted.lastIncreaseDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LastIncreaseDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_LastDecreaseDateTime().is_Some()) {
      converted.lastDecreaseDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LastDecreaseDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_NumberOfDecreasesToday().is_Some()) {
      converted.numberOfDecreasesToday((dafnyValue.dtor_NumberOfDecreasesToday().dtor_value()));
    }
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      converted.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      converted.writeCapacityUnits((dafnyValue.dtor_WriteCapacityUnits().dtor_value()));
    }
    return converted.build();
  }

  public static BillingModeSummary BillingModeSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.BillingModeSummary dafnyValue) {
    BillingModeSummary.Builder converted = BillingModeSummary.builder();
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      converted.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdateToPayPerRequestDateTime().is_Some()) {
      converted.lastUpdateToPayPerRequestDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LastUpdateToPayPerRequestDateTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static List<LocalSecondaryIndexDescription> LocalSecondaryIndexDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::LocalSecondaryIndexDescription);
  }

  public static List<GlobalSecondaryIndexDescription> GlobalSecondaryIndexDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalSecondaryIndexDescription);
  }

  public static RestoreSummary RestoreSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.RestoreSummary dafnyValue) {
    RestoreSummary.Builder converted = RestoreSummary.builder();
    if (dafnyValue.dtor_SourceBackupArn().is_Some()) {
      converted.sourceBackupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceBackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableArn().is_Some()) {
      converted.sourceTableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableArn().dtor_value()));
    }
    converted.restoreDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_RestoreDateTime()).toInstant());
    converted.restoreInProgress((dafnyValue.dtor_RestoreInProgress()));
    return converted.build();
  }

  public static SSEDescription SSEDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.SSEDescription dafnyValue) {
    SSEDescription.Builder converted = SSEDescription.builder();
    if (dafnyValue.dtor_Status().is_Some()) {
      converted.status(ToNative.SSEStatus(dafnyValue.dtor_Status().dtor_value()));
    }
    if (dafnyValue.dtor_SSEType().is_Some()) {
      converted.sseType(ToNative.SSEType(dafnyValue.dtor_SSEType().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyArn().is_Some()) {
      converted.kmsMasterKeyArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyArn().dtor_value()));
    }
    if (dafnyValue.dtor_InaccessibleEncryptionDateTime().is_Some()) {
      converted.inaccessibleEncryptionDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_InaccessibleEncryptionDateTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static ArchivalSummary ArchivalSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.ArchivalSummary dafnyValue) {
    ArchivalSummary.Builder converted = ArchivalSummary.builder();
    if (dafnyValue.dtor_ArchivalDateTime().is_Some()) {
      converted.archivalDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_ArchivalDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ArchivalReason().is_Some()) {
      converted.archivalReason(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ArchivalReason().dtor_value()));
    }
    if (dafnyValue.dtor_ArchivalBackupArn().is_Some()) {
      converted.archivalBackupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ArchivalBackupArn().dtor_value()));
    }
    return converted.build();
  }

  public static TableClassSummary TableClassSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.TableClassSummary dafnyValue) {
    TableClassSummary.Builder converted = TableClassSummary.builder();
    if (dafnyValue.dtor_TableClass().is_Some()) {
      converted.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdateDateTime().is_Some()) {
      converted.lastUpdateDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LastUpdateDateTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static SourceTableDetails SourceTableDetails(
      Dafny.Com.Amazonaws.Dynamodb.Types.SourceTableDetails dafnyValue) {
    SourceTableDetails.Builder converted = SourceTableDetails.builder();
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.tableId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId()));
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableSizeBytes().is_Some()) {
      converted.tableSizeBytes((dafnyValue.dtor_TableSizeBytes().dtor_value()));
    }
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    converted.tableCreationDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_TableCreationDateTime()).toInstant());
    converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput()));
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      converted.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      converted.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    return converted.build();
  }

  public static SourceTableFeatureDetails SourceTableFeatureDetails(
      Dafny.Com.Amazonaws.Dynamodb.Types.SourceTableFeatureDetails dafnyValue) {
    SourceTableFeatureDetails.Builder converted = SourceTableFeatureDetails.builder();
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      converted.localSecondaryIndexes(ToNative.LocalSecondaryIndexes(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexes(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_StreamDescription().is_Some()) {
      converted.streamDescription(ToNative.StreamSpecification(dafnyValue.dtor_StreamDescription().dtor_value()));
    }
    if (dafnyValue.dtor_TimeToLiveDescription().is_Some()) {
      converted.timeToLiveDescription(ToNative.TimeToLiveDescription(dafnyValue.dtor_TimeToLiveDescription().dtor_value()));
    }
    if (dafnyValue.dtor_SSEDescription().is_Some()) {
      converted.sseDescription(ToNative.SSEDescription(dafnyValue.dtor_SSEDescription().dtor_value()));
    }
    return converted.build();
  }

  public static Capacity Capacity(Dafny.Com.Amazonaws.Dynamodb.Types.Capacity dafnyValue) {
    Capacity.Builder converted = Capacity.builder();
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      converted.readCapacityUnits(Double.valueOf(dafnyValue.dtor_ReadCapacityUnits().dtor_value().intValue()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      converted.writeCapacityUnits(Double.valueOf(dafnyValue.dtor_WriteCapacityUnits().dtor_value().intValue()));
    }
    if (dafnyValue.dtor_CapacityUnits().is_Some()) {
      converted.capacityUnits(Double.valueOf(dafnyValue.dtor_CapacityUnits().dtor_value().intValue()));
    }
    return converted.build();
  }

  public static Map<String, Capacity> SecondaryIndexesCapacityMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.Capacity> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Capacity);
  }

  public static Map<String, AttributeValue> ItemCollectionKeyAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static List<Double> ItemCollectionSizeEstimateRange(
      DafnySequence<? extends Integer> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Function.identity()).stream().map(val -> Double.valueOf(val.intValue())).collect(Collectors.toList());
  }

  public static ContinuousBackupsStatus ContinuousBackupsStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.ContinuousBackupsStatus dafnyValue) {
    if (dafnyValue.is_ENABLED()) {
      return ContinuousBackupsStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLED()) {
      return ContinuousBackupsStatus.DISABLED;
    }
    return ContinuousBackupsStatus.fromValue(dafnyValue.toString());
  }

  public static PointInTimeRecoveryDescription PointInTimeRecoveryDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.PointInTimeRecoveryDescription dafnyValue) {
    PointInTimeRecoveryDescription.Builder converted = PointInTimeRecoveryDescription.builder();
    if (dafnyValue.dtor_PointInTimeRecoveryStatus().is_Some()) {
      converted.pointInTimeRecoveryStatus(ToNative.PointInTimeRecoveryStatus(dafnyValue.dtor_PointInTimeRecoveryStatus().dtor_value()));
    }
    if (dafnyValue.dtor_EarliestRestorableDateTime().is_Some()) {
      converted.earliestRestorableDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_EarliestRestorableDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_LatestRestorableDateTime().is_Some()) {
      converted.latestRestorableDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_LatestRestorableDateTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static Endpoint Endpoint(Dafny.Com.Amazonaws.Dynamodb.Types.Endpoint dafnyValue) {
    Endpoint.Builder converted = Endpoint.builder();
    converted.address(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Address()));
    converted.cachePeriodInMinutes((dafnyValue.dtor_CachePeriodInMinutes()));
    return converted.build();
  }

  public static ExportStatus ExportStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportStatus dafnyValue) {
    if (dafnyValue.is_IN__PROGRESS()) {
      return ExportStatus.IN_PROGRESS;
    }
    if (dafnyValue.is_COMPLETED()) {
      return ExportStatus.COMPLETED;
    }
    if (dafnyValue.is_FAILED()) {
      return ExportStatus.FAILED;
    }
    return ExportStatus.fromValue(dafnyValue.toString());
  }

  public static ReplicaSettingsDescription ReplicaSettingsDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaSettingsDescription dafnyValue) {
    ReplicaSettingsDescription.Builder converted = ReplicaSettingsDescription.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      converted.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaBillingModeSummary().is_Some()) {
      converted.replicaBillingModeSummary(ToNative.BillingModeSummary(dafnyValue.dtor_ReplicaBillingModeSummary().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().is_Some()) {
      converted.replicaProvisionedReadCapacityUnits((dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      converted.replicaProvisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityUnits().is_Some()) {
      converted.replicaProvisionedWriteCapacityUnits((dafnyValue.dtor_ReplicaProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      converted.replicaProvisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettings().is_Some()) {
      converted.replicaGlobalSecondaryIndexSettings(ToNative.ReplicaGlobalSecondaryIndexSettingsDescriptionList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTableClassSummary().is_Some()) {
      converted.replicaTableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_ReplicaTableClassSummary().dtor_value()));
    }
    return converted.build();
  }

  public static ImportStatus ImportStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.ImportStatus dafnyValue) {
    if (dafnyValue.is_IN__PROGRESS()) {
      return ImportStatus.IN_PROGRESS;
    }
    if (dafnyValue.is_COMPLETED()) {
      return ImportStatus.COMPLETED;
    }
    if (dafnyValue.is_CANCELLING()) {
      return ImportStatus.CANCELLING;
    }
    if (dafnyValue.is_CANCELLED()) {
      return ImportStatus.CANCELLED;
    }
    if (dafnyValue.is_FAILED()) {
      return ImportStatus.FAILED;
    }
    return ImportStatus.fromValue(dafnyValue.toString());
  }

  public static KinesisDataStreamDestination KinesisDataStreamDestination(
      Dafny.Com.Amazonaws.Dynamodb.Types.KinesisDataStreamDestination dafnyValue) {
    KinesisDataStreamDestination.Builder converted = KinesisDataStreamDestination.builder();
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      converted.streamArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      converted.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationStatusDescription().is_Some()) {
      converted.destinationStatusDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_DestinationStatusDescription().dtor_value()));
    }
    return converted.build();
  }

  public static List<ReplicaAutoScalingDescription> ReplicaAutoScalingDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaAutoScalingDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaAutoScalingDescription);
  }

  public static TimeToLiveStatus TimeToLiveStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.TimeToLiveStatus dafnyValue) {
    if (dafnyValue.is_ENABLING()) {
      return TimeToLiveStatus.ENABLING;
    }
    if (dafnyValue.is_DISABLING()) {
      return TimeToLiveStatus.DISABLING;
    }
    if (dafnyValue.is_ENABLED()) {
      return TimeToLiveStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLED()) {
      return TimeToLiveStatus.DISABLED;
    }
    return TimeToLiveStatus.fromValue(dafnyValue.toString());
  }

  public static ItemResponse ItemResponse(
      Dafny.Com.Amazonaws.Dynamodb.Types.ItemResponse dafnyValue) {
    ItemResponse.Builder converted = ItemResponse.builder();
    if (dafnyValue.dtor_Item().is_Some()) {
      converted.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    return converted.build();
  }

  public static BackupSummary BackupSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.BackupSummary dafnyValue) {
    BackupSummary.Builder converted = BackupSummary.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      converted.tableId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_BackupArn().is_Some()) {
      converted.backupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_BackupName().is_Some()) {
      converted.backupName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName().dtor_value()));
    }
    if (dafnyValue.dtor_BackupCreationDateTime().is_Some()) {
      converted.backupCreationDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_BackupCreationDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_BackupExpiryDateTime().is_Some()) {
      converted.backupExpiryDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_BackupExpiryDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_BackupStatus().is_Some()) {
      converted.backupStatus(ToNative.BackupStatus(dafnyValue.dtor_BackupStatus().dtor_value()));
    }
    if (dafnyValue.dtor_BackupType().is_Some()) {
      converted.backupType(ToNative.BackupType(dafnyValue.dtor_BackupType().dtor_value()));
    }
    if (dafnyValue.dtor_BackupSizeBytes().is_Some()) {
      converted.backupSizeBytes((dafnyValue.dtor_BackupSizeBytes().dtor_value()));
    }
    return converted.build();
  }

  public static ContributorInsightsSummary ContributorInsightsSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.ContributorInsightsSummary dafnyValue) {
    ContributorInsightsSummary.Builder converted = ContributorInsightsSummary.builder();
    if (dafnyValue.dtor_TableName().is_Some()) {
      converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      converted.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    return converted.build();
  }

  public static ExportSummary ExportSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.ExportSummary dafnyValue) {
    ExportSummary.Builder converted = ExportSummary.builder();
    if (dafnyValue.dtor_ExportArn().is_Some()) {
      converted.exportArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ExportStatus().is_Some()) {
      converted.exportStatus(ToNative.ExportStatus(dafnyValue.dtor_ExportStatus().dtor_value()));
    }
    return converted.build();
  }

  public static GlobalTable GlobalTable(Dafny.Com.Amazonaws.Dynamodb.Types.GlobalTable dafnyValue) {
    GlobalTable.Builder converted = GlobalTable.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      converted.globalTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicationGroup().is_Some()) {
      converted.replicationGroup(ToNative.ReplicaList(dafnyValue.dtor_ReplicationGroup().dtor_value()));
    }
    return converted.build();
  }

  public static ImportSummary ImportSummary(
      Dafny.Com.Amazonaws.Dynamodb.Types.ImportSummary dafnyValue) {
    ImportSummary.Builder converted = ImportSummary.builder();
    if (dafnyValue.dtor_ImportArn().is_Some()) {
      converted.importArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ImportStatus().is_Some()) {
      converted.importStatus(ToNative.ImportStatus(dafnyValue.dtor_ImportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      converted.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketSource().is_Some()) {
      converted.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource().dtor_value()));
    }
    if (dafnyValue.dtor_CloudWatchLogGroupArn().is_Some()) {
      converted.cloudWatchLogGroupArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudWatchLogGroupArn().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormat().is_Some()) {
      converted.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      converted.startTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_StartTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      converted.endTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_EndTime().dtor_value()).toInstant());
    }
    return converted.build();
  }

  public static List<Map<String, AttributeValue>> KeyList(
      DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::Key);
  }

  public static WriteRequest WriteRequest(
      Dafny.Com.Amazonaws.Dynamodb.Types.WriteRequest dafnyValue) {
    WriteRequest.Builder converted = WriteRequest.builder();
    if (dafnyValue.dtor_PutRequest().is_Some()) {
      converted.putRequest(ToNative.PutRequest(dafnyValue.dtor_PutRequest().dtor_value()));
    }
    if (dafnyValue.dtor_DeleteRequest().is_Some()) {
      converted.deleteRequest(ToNative.DeleteRequest(dafnyValue.dtor_DeleteRequest().dtor_value()));
    }
    return converted.build();
  }

  public static ScalarAttributeType ScalarAttributeType(
      Dafny.Com.Amazonaws.Dynamodb.Types.ScalarAttributeType dafnyValue) {
    if (dafnyValue.is_S()) {
      return ScalarAttributeType.S;
    }
    if (dafnyValue.is_N()) {
      return ScalarAttributeType.N;
    }
    if (dafnyValue.is_B()) {
      return ScalarAttributeType.B;
    }
    return ScalarAttributeType.fromValue(dafnyValue.toString());
  }

  public static KeyType KeyType(Dafny.Com.Amazonaws.Dynamodb.Types.KeyType dafnyValue) {
    if (dafnyValue.is_HASH()) {
      return KeyType.HASH;
    }
    if (dafnyValue.is_RANGE()) {
      return KeyType.RANGE;
    }
    return KeyType.fromValue(dafnyValue.toString());
  }

  public static Projection Projection(Dafny.Com.Amazonaws.Dynamodb.Types.Projection dafnyValue) {
    Projection.Builder converted = Projection.builder();
    if (dafnyValue.dtor_ProjectionType().is_Some()) {
      converted.projectionType(ToNative.ProjectionType(dafnyValue.dtor_ProjectionType().dtor_value()));
    }
    if (dafnyValue.dtor_NonKeyAttributes().is_Some()) {
      converted.nonKeyAttributes(ToNative.NonKeyAttributeNameList(dafnyValue.dtor_NonKeyAttributes().dtor_value()));
    }
    return converted.build();
  }

  public static List<String> StringSetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> NumberSetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static List<ByteBuffer> BinarySetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::ByteBuffer);
  }

  public static Map<String, AttributeValue> MapAttributeValue(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static List<AttributeValue> ListAttributeValue(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static ComparisonOperator ComparisonOperator(
      Dafny.Com.Amazonaws.Dynamodb.Types.ComparisonOperator dafnyValue) {
    if (dafnyValue.is_EQ()) {
      return ComparisonOperator.EQ;
    }
    if (dafnyValue.is_NE()) {
      return ComparisonOperator.NE;
    }
    if (dafnyValue.is_IN()) {
      return ComparisonOperator.IN;
    }
    if (dafnyValue.is_LE()) {
      return ComparisonOperator.LE;
    }
    if (dafnyValue.is_LT()) {
      return ComparisonOperator.LT;
    }
    if (dafnyValue.is_GE()) {
      return ComparisonOperator.GE;
    }
    if (dafnyValue.is_GT()) {
      return ComparisonOperator.GT;
    }
    if (dafnyValue.is_BETWEEN()) {
      return ComparisonOperator.BETWEEN;
    }
    if (dafnyValue.is_NOT__NULL()) {
      return ComparisonOperator.NOT_NULL;
    }
    if (dafnyValue.is_NULL()) {
      return ComparisonOperator.NULL;
    }
    if (dafnyValue.is_CONTAINS()) {
      return ComparisonOperator.CONTAINS;
    }
    if (dafnyValue.is_NOT__CONTAINS()) {
      return ComparisonOperator.NOT_CONTAINS;
    }
    if (dafnyValue.is_BEGINS__WITH()) {
      return ComparisonOperator.BEGINS_WITH;
    }
    return ComparisonOperator.fromValue(dafnyValue.toString());
  }

  public static List<AttributeValue> AttributeValueList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.AttributeValue> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AttributeValue);
  }

  public static List<String> CsvHeaderList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static Get Get(Dafny.Com.Amazonaws.Dynamodb.Types.Get dafnyValue) {
    Get.Builder converted = Get.builder();
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      converted.projectionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    return converted.build();
  }

  public static ConditionCheck ConditionCheck(
      Dafny.Com.Amazonaws.Dynamodb.Types.ConditionCheck dafnyValue) {
    ConditionCheck.Builder converted = ConditionCheck.builder();
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression()));
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      converted.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    return converted.build();
  }

  public static Put Put(Dafny.Com.Amazonaws.Dynamodb.Types.Put dafnyValue) {
    Put.Builder converted = Put.builder();
    converted.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      converted.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    return converted.build();
  }

  public static Delete Delete(Dafny.Com.Amazonaws.Dynamodb.Types.Delete dafnyValue) {
    Delete.Builder converted = Delete.builder();
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      converted.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    return converted.build();
  }

  public static Update Update(Dafny.Com.Amazonaws.Dynamodb.Types.Update dafnyValue) {
    Update.Builder converted = Update.builder();
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    converted.updateExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_UpdateExpression()));
    converted.tableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      converted.conditionExpression(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      converted.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      converted.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      converted.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    return converted.build();
  }

  public static CreateReplicaAction CreateReplicaAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateReplicaAction dafnyValue) {
    CreateReplicaAction.Builder converted = CreateReplicaAction.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return converted.build();
  }

  public static DeleteReplicaAction DeleteReplicaAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteReplicaAction dafnyValue) {
    DeleteReplicaAction.Builder converted = DeleteReplicaAction.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return converted.build();
  }

  public static AutoScalingTargetTrackingScalingPolicyConfigurationUpdate AutoScalingTargetTrackingScalingPolicyConfigurationUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingTargetTrackingScalingPolicyConfigurationUpdate dafnyValue) {
    AutoScalingTargetTrackingScalingPolicyConfigurationUpdate.Builder converted = AutoScalingTargetTrackingScalingPolicyConfigurationUpdate.builder();
    if (dafnyValue.dtor_DisableScaleIn().is_Some()) {
      converted.disableScaleIn((dafnyValue.dtor_DisableScaleIn().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleInCooldown().is_Some()) {
      converted.scaleInCooldown((dafnyValue.dtor_ScaleInCooldown().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleOutCooldown().is_Some()) {
      converted.scaleOutCooldown((dafnyValue.dtor_ScaleOutCooldown().dtor_value()));
    }
    converted.targetValue(Double.valueOf(dafnyValue.dtor_TargetValue()));
    return converted.build();
  }

  public static List<ReplicaGlobalSecondaryIndexSettingsUpdate> ReplicaGlobalSecondaryIndexSettingsUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexSettingsUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndexSettingsUpdate);
  }

  public static AttributeAction AttributeAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.AttributeAction dafnyValue) {
    if (dafnyValue.is_ADD()) {
      return AttributeAction.ADD;
    }
    if (dafnyValue.is_PUT()) {
      return AttributeAction.PUT;
    }
    if (dafnyValue.is_DELETE()) {
      return AttributeAction.DELETE;
    }
    return AttributeAction.fromValue(dafnyValue.toString());
  }

  public static UpdateGlobalSecondaryIndexAction UpdateGlobalSecondaryIndexAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateGlobalSecondaryIndexAction dafnyValue) {
    UpdateGlobalSecondaryIndexAction.Builder converted = UpdateGlobalSecondaryIndexAction.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput()));
    return converted.build();
  }

  public static CreateGlobalSecondaryIndexAction CreateGlobalSecondaryIndexAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateGlobalSecondaryIndexAction dafnyValue) {
    CreateGlobalSecondaryIndexAction.Builder converted = CreateGlobalSecondaryIndexAction.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    converted.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return converted.build();
  }

  public static DeleteGlobalSecondaryIndexAction DeleteGlobalSecondaryIndexAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteGlobalSecondaryIndexAction dafnyValue) {
    DeleteGlobalSecondaryIndexAction.Builder converted = DeleteGlobalSecondaryIndexAction.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    return converted.build();
  }

  public static CreateReplicationGroupMemberAction CreateReplicationGroupMemberAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.CreateReplicationGroupMemberAction dafnyValue) {
    CreateReplicationGroupMemberAction.Builder converted = CreateReplicationGroupMemberAction.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      converted.kmsMasterKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_TableClassOverride().is_Some()) {
      converted.tableClassOverride(ToNative.TableClass(dafnyValue.dtor_TableClassOverride().dtor_value()));
    }
    return converted.build();
  }

  public static UpdateReplicationGroupMemberAction UpdateReplicationGroupMemberAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.UpdateReplicationGroupMemberAction dafnyValue) {
    UpdateReplicationGroupMemberAction.Builder converted = UpdateReplicationGroupMemberAction.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      converted.kmsMasterKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_TableClassOverride().is_Some()) {
      converted.tableClassOverride(ToNative.TableClass(dafnyValue.dtor_TableClassOverride().dtor_value()));
    }
    return converted.build();
  }

  public static DeleteReplicationGroupMemberAction DeleteReplicationGroupMemberAction(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteReplicationGroupMemberAction dafnyValue) {
    DeleteReplicationGroupMemberAction.Builder converted = DeleteReplicationGroupMemberAction.builder();
    converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return converted.build();
  }

  public static List<ReplicaGlobalSecondaryIndexAutoScalingUpdate> ReplicaGlobalSecondaryIndexAutoScalingUpdateList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexAutoScalingUpdate> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndexAutoScalingUpdate);
  }

  public static BatchStatementError BatchStatementError(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementError dafnyValue) {
    BatchStatementError.Builder converted = BatchStatementError.builder();
    if (dafnyValue.dtor_Code().is_Some()) {
      converted.code(ToNative.BatchStatementErrorCodeEnum(dafnyValue.dtor_Code().dtor_value()));
    }
    if (dafnyValue.dtor_Message().is_Some()) {
      converted.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaDescription ReplicaDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaDescription dafnyValue) {
    ReplicaDescription.Builder converted = ReplicaDescription.builder();
    if (dafnyValue.dtor_RegionName().is_Some()) {
      converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      converted.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatusDescription().is_Some()) {
      converted.replicaStatusDescription(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaStatusDescription().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatusPercentProgress().is_Some()) {
      converted.replicaStatusPercentProgress(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaStatusPercentProgress().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      converted.kmsMasterKeyId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaInaccessibleDateTime().is_Some()) {
      converted.replicaInaccessibleDateTime(software.amazon.dafny.conversion.ToNative.Simple.Date(dafnyValue.dtor_ReplicaInaccessibleDateTime().dtor_value()).toInstant());
    }
    if (dafnyValue.dtor_ReplicaTableClassSummary().is_Some()) {
      converted.replicaTableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_ReplicaTableClassSummary().dtor_value()));
    }
    return converted.build();
  }

  public static LocalSecondaryIndexDescription LocalSecondaryIndexDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndexDescription dafnyValue) {
    LocalSecondaryIndexDescription.Builder converted = LocalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      converted.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    if (dafnyValue.dtor_IndexSizeBytes().is_Some()) {
      converted.indexSizeBytes((dafnyValue.dtor_IndexSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      converted.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_IndexArn().is_Some()) {
      converted.indexArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexArn().dtor_value()));
    }
    return converted.build();
  }

  public static GlobalSecondaryIndexDescription GlobalSecondaryIndexDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexDescription dafnyValue) {
    GlobalSecondaryIndexDescription.Builder converted = GlobalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      converted.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      converted.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_Backfilling().is_Some()) {
      converted.backfilling((dafnyValue.dtor_Backfilling().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughputDescription(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_IndexSizeBytes().is_Some()) {
      converted.indexSizeBytes((dafnyValue.dtor_IndexSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      converted.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_IndexArn().is_Some()) {
      converted.indexArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexArn().dtor_value()));
    }
    return converted.build();
  }

  public static SSEStatus SSEStatus(Dafny.Com.Amazonaws.Dynamodb.Types.SSEStatus dafnyValue) {
    if (dafnyValue.is_ENABLING()) {
      return SSEStatus.ENABLING;
    }
    if (dafnyValue.is_ENABLED()) {
      return SSEStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLING()) {
      return SSEStatus.DISABLING;
    }
    if (dafnyValue.is_DISABLED()) {
      return SSEStatus.DISABLED;
    }
    if (dafnyValue.is_UPDATING()) {
      return SSEStatus.UPDATING;
    }
    return SSEStatus.fromValue(dafnyValue.toString());
  }

  public static List<LocalSecondaryIndexInfo> LocalSecondaryIndexes(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndexInfo> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::LocalSecondaryIndexInfo);
  }

  public static List<GlobalSecondaryIndexInfo> GlobalSecondaryIndexes(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexInfo> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::GlobalSecondaryIndexInfo);
  }

  public static PointInTimeRecoveryStatus PointInTimeRecoveryStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.PointInTimeRecoveryStatus dafnyValue) {
    if (dafnyValue.is_ENABLED()) {
      return PointInTimeRecoveryStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLED()) {
      return PointInTimeRecoveryStatus.DISABLED;
    }
    return PointInTimeRecoveryStatus.fromValue(dafnyValue.toString());
  }

  public static ReplicaStatus ReplicaStatus(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaStatus dafnyValue) {
    if (dafnyValue.is_CREATING()) {
      return ReplicaStatus.CREATING;
    }
    if (dafnyValue.is_CREATION__FAILED()) {
      return ReplicaStatus.CREATION_FAILED;
    }
    if (dafnyValue.is_UPDATING()) {
      return ReplicaStatus.UPDATING;
    }
    if (dafnyValue.is_DELETING()) {
      return ReplicaStatus.DELETING;
    }
    if (dafnyValue.is_ACTIVE()) {
      return ReplicaStatus.ACTIVE;
    }
    if (dafnyValue.is_REGION__DISABLED()) {
      return ReplicaStatus.REGION_DISABLED;
    }
    if (dafnyValue.is_INACCESSIBLE__ENCRYPTION__CREDENTIALS()) {
      return ReplicaStatus.INACCESSIBLE_ENCRYPTION_CREDENTIALS;
    }
    return ReplicaStatus.fromValue(dafnyValue.toString());
  }

  public static AutoScalingSettingsDescription AutoScalingSettingsDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingSettingsDescription dafnyValue) {
    AutoScalingSettingsDescription.Builder converted = AutoScalingSettingsDescription.builder();
    if (dafnyValue.dtor_MinimumUnits().is_Some()) {
      converted.minimumUnits((dafnyValue.dtor_MinimumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_MaximumUnits().is_Some()) {
      converted.maximumUnits((dafnyValue.dtor_MaximumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingDisabled().is_Some()) {
      converted.autoScalingDisabled((dafnyValue.dtor_AutoScalingDisabled().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingRoleArn().is_Some()) {
      converted.autoScalingRoleArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AutoScalingRoleArn().dtor_value()));
    }
    if (dafnyValue.dtor_ScalingPolicies().is_Some()) {
      converted.scalingPolicies(ToNative.AutoScalingPolicyDescriptionList(dafnyValue.dtor_ScalingPolicies().dtor_value()));
    }
    return converted.build();
  }

  public static List<ReplicaGlobalSecondaryIndexSettingsDescription> ReplicaGlobalSecondaryIndexSettingsDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexSettingsDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndexSettingsDescription);
  }

  public static ReplicaAutoScalingDescription ReplicaAutoScalingDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaAutoScalingDescription dafnyValue) {
    ReplicaAutoScalingDescription.Builder converted = ReplicaAutoScalingDescription.builder();
    if (dafnyValue.dtor_RegionName().is_Some()) {
      converted.regionName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      converted.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexAutoScalingDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      converted.replicaProvisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      converted.replicaProvisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      converted.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    return converted.build();
  }

  public static PutRequest PutRequest(Dafny.Com.Amazonaws.Dynamodb.Types.PutRequest dafnyValue) {
    PutRequest.Builder converted = PutRequest.builder();
    converted.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    return converted.build();
  }

  public static DeleteRequest DeleteRequest(
      Dafny.Com.Amazonaws.Dynamodb.Types.DeleteRequest dafnyValue) {
    DeleteRequest.Builder converted = DeleteRequest.builder();
    converted.key(ToNative.Key(dafnyValue.dtor_Key()));
    return converted.build();
  }

  public static ProjectionType ProjectionType(
      Dafny.Com.Amazonaws.Dynamodb.Types.ProjectionType dafnyValue) {
    if (dafnyValue.is_ALL()) {
      return ProjectionType.ALL;
    }
    if (dafnyValue.is_KEYS__ONLY()) {
      return ProjectionType.KEYS_ONLY;
    }
    if (dafnyValue.is_INCLUDE()) {
      return ProjectionType.INCLUDE;
    }
    return ProjectionType.fromValue(dafnyValue.toString());
  }

  public static List<String> NonKeyAttributeNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static ReturnValuesOnConditionCheckFailure ReturnValuesOnConditionCheckFailure(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReturnValuesOnConditionCheckFailure dafnyValue) {
    if (dafnyValue.is_ALL__OLD()) {
      return ReturnValuesOnConditionCheckFailure.ALL_OLD;
    }
    if (dafnyValue.is_NONE()) {
      return ReturnValuesOnConditionCheckFailure.NONE;
    }
    return ReturnValuesOnConditionCheckFailure.fromValue(dafnyValue.toString());
  }

  public static ReplicaGlobalSecondaryIndexSettingsUpdate ReplicaGlobalSecondaryIndexSettingsUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexSettingsUpdate dafnyValue) {
    ReplicaGlobalSecondaryIndexSettingsUpdate.Builder converted = ReplicaGlobalSecondaryIndexSettingsUpdate.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedReadCapacityUnits().is_Some()) {
      converted.provisionedReadCapacityUnits((dafnyValue.dtor_ProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettingsUpdate().is_Some()) {
      converted.provisionedReadCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static ProvisionedThroughputOverride ProvisionedThroughputOverride(
      Dafny.Com.Amazonaws.Dynamodb.Types.ProvisionedThroughputOverride dafnyValue) {
    ProvisionedThroughputOverride.Builder converted = ProvisionedThroughputOverride.builder();
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      converted.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    return converted.build();
  }

  public static List<ReplicaGlobalSecondaryIndex> ReplicaGlobalSecondaryIndexList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndex> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndex);
  }

  public static ReplicaGlobalSecondaryIndexAutoScalingUpdate ReplicaGlobalSecondaryIndexAutoScalingUpdate(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexAutoScalingUpdate dafnyValue) {
    ReplicaGlobalSecondaryIndexAutoScalingUpdate.Builder converted = ReplicaGlobalSecondaryIndexAutoScalingUpdate.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingUpdate().is_Some()) {
      converted.provisionedReadCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingUpdate().dtor_value()));
    }
    return converted.build();
  }

  public static BatchStatementErrorCodeEnum BatchStatementErrorCodeEnum(
      Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementErrorCodeEnum dafnyValue) {
    if (dafnyValue.is_ConditionalCheckFailed()) {
      return BatchStatementErrorCodeEnum.CONDITIONAL_CHECK_FAILED;
    }
    if (dafnyValue.is_ItemCollectionSizeLimitExceeded()) {
      return BatchStatementErrorCodeEnum.ITEM_COLLECTION_SIZE_LIMIT_EXCEEDED;
    }
    if (dafnyValue.is_RequestLimitExceeded()) {
      return BatchStatementErrorCodeEnum.REQUEST_LIMIT_EXCEEDED;
    }
    if (dafnyValue.is_ValidationError()) {
      return BatchStatementErrorCodeEnum.VALIDATION_ERROR;
    }
    if (dafnyValue.is_ProvisionedThroughputExceeded()) {
      return BatchStatementErrorCodeEnum.PROVISIONED_THROUGHPUT_EXCEEDED;
    }
    if (dafnyValue.is_TransactionConflict()) {
      return BatchStatementErrorCodeEnum.TRANSACTION_CONFLICT;
    }
    if (dafnyValue.is_ThrottlingError()) {
      return BatchStatementErrorCodeEnum.THROTTLING_ERROR;
    }
    if (dafnyValue.is_InternalServerError()) {
      return BatchStatementErrorCodeEnum.INTERNAL_SERVER_ERROR;
    }
    if (dafnyValue.is_ResourceNotFound()) {
      return BatchStatementErrorCodeEnum.RESOURCE_NOT_FOUND;
    }
    if (dafnyValue.is_AccessDenied()) {
      return BatchStatementErrorCodeEnum.ACCESS_DENIED;
    }
    if (dafnyValue.is_DuplicateItem()) {
      return BatchStatementErrorCodeEnum.DUPLICATE_ITEM;
    }
    return BatchStatementErrorCodeEnum.UNKNOWN_TO_SDK_VERSION;
  }

  public static List<ReplicaGlobalSecondaryIndexDescription> ReplicaGlobalSecondaryIndexDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndexDescription);
  }

  public static IndexStatus IndexStatus(Dafny.Com.Amazonaws.Dynamodb.Types.IndexStatus dafnyValue) {
    if (dafnyValue.is_CREATING()) {
      return IndexStatus.CREATING;
    }
    if (dafnyValue.is_UPDATING()) {
      return IndexStatus.UPDATING;
    }
    if (dafnyValue.is_DELETING()) {
      return IndexStatus.DELETING;
    }
    if (dafnyValue.is_ACTIVE()) {
      return IndexStatus.ACTIVE;
    }
    return IndexStatus.fromValue(dafnyValue.toString());
  }

  public static LocalSecondaryIndexInfo LocalSecondaryIndexInfo(
      Dafny.Com.Amazonaws.Dynamodb.Types.LocalSecondaryIndexInfo dafnyValue) {
    LocalSecondaryIndexInfo.Builder converted = LocalSecondaryIndexInfo.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      converted.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    return converted.build();
  }

  public static GlobalSecondaryIndexInfo GlobalSecondaryIndexInfo(
      Dafny.Com.Amazonaws.Dynamodb.Types.GlobalSecondaryIndexInfo dafnyValue) {
    GlobalSecondaryIndexInfo.Builder converted = GlobalSecondaryIndexInfo.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      converted.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      converted.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      converted.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return converted.build();
  }

  public static List<AutoScalingPolicyDescription> AutoScalingPolicyDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingPolicyDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::AutoScalingPolicyDescription);
  }

  public static ReplicaGlobalSecondaryIndexSettingsDescription ReplicaGlobalSecondaryIndexSettingsDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexSettingsDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexSettingsDescription.Builder converted = ReplicaGlobalSecondaryIndexSettingsDescription.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      converted.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityUnits().is_Some()) {
      converted.provisionedReadCapacityUnits((dafnyValue.dtor_ProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      converted.provisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityUnits().is_Some()) {
      converted.provisionedWriteCapacityUnits((dafnyValue.dtor_ProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      converted.provisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    return converted.build();
  }

  public static List<ReplicaGlobalSecondaryIndexAutoScalingDescription> ReplicaGlobalSecondaryIndexAutoScalingDescriptionList(
      DafnySequence<? extends Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexAutoScalingDescription> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        Dafny.Com.Amazonaws.Dynamodb.ToNative::ReplicaGlobalSecondaryIndexAutoScalingDescription);
  }

  public static ReplicaGlobalSecondaryIndex ReplicaGlobalSecondaryIndex(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndex dafnyValue) {
    ReplicaGlobalSecondaryIndex.Builder converted = ReplicaGlobalSecondaryIndex.builder();
    converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaGlobalSecondaryIndexDescription ReplicaGlobalSecondaryIndexDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexDescription.Builder converted = ReplicaGlobalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      converted.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    return converted.build();
  }

  public static AutoScalingPolicyDescription AutoScalingPolicyDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingPolicyDescription dafnyValue) {
    AutoScalingPolicyDescription.Builder converted = AutoScalingPolicyDescription.builder();
    if (dafnyValue.dtor_PolicyName().is_Some()) {
      converted.policyName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName().dtor_value()));
    }
    if (dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration().is_Some()) {
      converted.targetTrackingScalingPolicyConfiguration(ToNative.AutoScalingTargetTrackingScalingPolicyConfigurationDescription(dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration().dtor_value()));
    }
    return converted.build();
  }

  public static ReplicaGlobalSecondaryIndexAutoScalingDescription ReplicaGlobalSecondaryIndexAutoScalingDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.ReplicaGlobalSecondaryIndexAutoScalingDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexAutoScalingDescription.Builder converted = ReplicaGlobalSecondaryIndexAutoScalingDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      converted.indexName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      converted.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      converted.provisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      converted.provisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    return converted.build();
  }

  public static AutoScalingTargetTrackingScalingPolicyConfigurationDescription AutoScalingTargetTrackingScalingPolicyConfigurationDescription(
      Dafny.Com.Amazonaws.Dynamodb.Types.AutoScalingTargetTrackingScalingPolicyConfigurationDescription dafnyValue) {
    AutoScalingTargetTrackingScalingPolicyConfigurationDescription.Builder converted = AutoScalingTargetTrackingScalingPolicyConfigurationDescription.builder();
    if (dafnyValue.dtor_DisableScaleIn().is_Some()) {
      converted.disableScaleIn((dafnyValue.dtor_DisableScaleIn().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleInCooldown().is_Some()) {
      converted.scaleInCooldown((dafnyValue.dtor_ScaleInCooldown().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleOutCooldown().is_Some()) {
      converted.scaleOutCooldown((dafnyValue.dtor_ScaleOutCooldown().dtor_value()));
    }
    converted.targetValue(Double.valueOf(dafnyValue.dtor_TargetValue()));
    return converted.build();
  }

  public static DynamoDbClient DynamoDB__20120810(IDynamoDB__20120810Client dafnyValue) {
    return ((Shim) dafnyValue).impl();
  }
}
