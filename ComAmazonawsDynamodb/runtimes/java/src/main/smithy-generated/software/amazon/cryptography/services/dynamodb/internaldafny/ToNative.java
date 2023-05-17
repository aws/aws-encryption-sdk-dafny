// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.dynamodb.internaldafny;

import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Double;
import java.lang.String;
import java.util.List;
import java.util.Map;
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
import software.amazon.awssdk.services.dynamodb.model.BackupInUseException;
import software.amazon.awssdk.services.dynamodb.model.BackupNotFoundException;
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
import software.amazon.awssdk.services.dynamodb.model.CancellationReason;
import software.amazon.awssdk.services.dynamodb.model.Capacity;
import software.amazon.awssdk.services.dynamodb.model.ComparisonOperator;
import software.amazon.awssdk.services.dynamodb.model.Condition;
import software.amazon.awssdk.services.dynamodb.model.ConditionCheck;
import software.amazon.awssdk.services.dynamodb.model.ConditionalCheckFailedException;
import software.amazon.awssdk.services.dynamodb.model.ConditionalOperator;
import software.amazon.awssdk.services.dynamodb.model.ConsumedCapacity;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsDescription;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsStatus;
import software.amazon.awssdk.services.dynamodb.model.ContinuousBackupsUnavailableException;
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
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTableResponse;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.DescribeTimeToLiveResponse;
import software.amazon.awssdk.services.dynamodb.model.DestinationStatus;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.DisableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.DuplicateItemException;
// BEGIN MANUAL EDIT
import software.amazon.awssdk.services.dynamodb.model.DynamoDbException;
// END MANUAL EDIT
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationRequest;
import software.amazon.awssdk.services.dynamodb.model.EnableKinesisStreamingDestinationResponse;
import software.amazon.awssdk.services.dynamodb.model.Endpoint;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteStatementResponse;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionRequest;
import software.amazon.awssdk.services.dynamodb.model.ExecuteTransactionResponse;
import software.amazon.awssdk.services.dynamodb.model.ExpectedAttributeValue;
import software.amazon.awssdk.services.dynamodb.model.ExportConflictException;
import software.amazon.awssdk.services.dynamodb.model.ExportDescription;
import software.amazon.awssdk.services.dynamodb.model.ExportFormat;
import software.amazon.awssdk.services.dynamodb.model.ExportNotFoundException;
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
import software.amazon.awssdk.services.dynamodb.model.GlobalTableAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableDescription;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableGlobalSecondaryIndexSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.GlobalTableStatus;
import software.amazon.awssdk.services.dynamodb.model.IdempotentParameterMismatchException;
import software.amazon.awssdk.services.dynamodb.model.ImportConflictException;
import software.amazon.awssdk.services.dynamodb.model.ImportNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.ImportStatus;
import software.amazon.awssdk.services.dynamodb.model.ImportSummary;
import software.amazon.awssdk.services.dynamodb.model.ImportTableDescription;
import software.amazon.awssdk.services.dynamodb.model.ImportTableRequest;
import software.amazon.awssdk.services.dynamodb.model.ImportTableResponse;
import software.amazon.awssdk.services.dynamodb.model.IndexNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.IndexStatus;
import software.amazon.awssdk.services.dynamodb.model.InputCompressionType;
import software.amazon.awssdk.services.dynamodb.model.InputFormat;
import software.amazon.awssdk.services.dynamodb.model.InputFormatOptions;
import software.amazon.awssdk.services.dynamodb.model.InternalServerErrorException;
import software.amazon.awssdk.services.dynamodb.model.InvalidExportTimeException;
import software.amazon.awssdk.services.dynamodb.model.InvalidRestoreTimeException;
import software.amazon.awssdk.services.dynamodb.model.ItemCollectionMetrics;
import software.amazon.awssdk.services.dynamodb.model.ItemCollectionSizeLimitExceededException;
import software.amazon.awssdk.services.dynamodb.model.ItemResponse;
import software.amazon.awssdk.services.dynamodb.model.KeySchemaElement;
import software.amazon.awssdk.services.dynamodb.model.KeyType;
import software.amazon.awssdk.services.dynamodb.model.KeysAndAttributes;
import software.amazon.awssdk.services.dynamodb.model.KinesisDataStreamDestination;
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
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndex;
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndexDescription;
import software.amazon.awssdk.services.dynamodb.model.LocalSecondaryIndexInfo;
import software.amazon.awssdk.services.dynamodb.model.ParameterizedStatement;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryDescription;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoverySpecification;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryStatus;
import software.amazon.awssdk.services.dynamodb.model.PointInTimeRecoveryUnavailableException;
import software.amazon.awssdk.services.dynamodb.model.Projection;
import software.amazon.awssdk.services.dynamodb.model.ProjectionType;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughput;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputDescription;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputExceededException;
import software.amazon.awssdk.services.dynamodb.model.ProvisionedThroughputOverride;
import software.amazon.awssdk.services.dynamodb.model.Put;
import software.amazon.awssdk.services.dynamodb.model.PutItemRequest;
import software.amazon.awssdk.services.dynamodb.model.PutItemResponse;
import software.amazon.awssdk.services.dynamodb.model.PutRequest;
import software.amazon.awssdk.services.dynamodb.model.QueryRequest;
import software.amazon.awssdk.services.dynamodb.model.QueryResponse;
import software.amazon.awssdk.services.dynamodb.model.Replica;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaAutoScalingUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndex;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexAutoScalingUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexSettingsDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaGlobalSecondaryIndexSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaNotFoundException;
import software.amazon.awssdk.services.dynamodb.model.ReplicaSettingsDescription;
import software.amazon.awssdk.services.dynamodb.model.ReplicaSettingsUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicaStatus;
import software.amazon.awssdk.services.dynamodb.model.ReplicaUpdate;
import software.amazon.awssdk.services.dynamodb.model.ReplicationGroupUpdate;
import software.amazon.awssdk.services.dynamodb.model.RequestLimitExceededException;
import software.amazon.awssdk.services.dynamodb.model.ResourceInUseException;
import software.amazon.awssdk.services.dynamodb.model.ResourceNotFoundException;
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
import software.amazon.awssdk.services.dynamodb.model.TableAlreadyExistsException;
import software.amazon.awssdk.services.dynamodb.model.TableAutoScalingDescription;
import software.amazon.awssdk.services.dynamodb.model.TableClass;
import software.amazon.awssdk.services.dynamodb.model.TableClassSummary;
import software.amazon.awssdk.services.dynamodb.model.TableCreationParameters;
import software.amazon.awssdk.services.dynamodb.model.TableDescription;
import software.amazon.awssdk.services.dynamodb.model.TableInUseException;
import software.amazon.awssdk.services.dynamodb.model.TableNotFoundException;
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
import software.amazon.awssdk.services.dynamodb.model.TransactionCanceledException;
import software.amazon.awssdk.services.dynamodb.model.TransactionConflictException;
import software.amazon.awssdk.services.dynamodb.model.TransactionInProgressException;
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
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableReplicaAutoScalingResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTableResponse;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveRequest;
import software.amazon.awssdk.services.dynamodb.model.UpdateTimeToLiveResponse;
import software.amazon.awssdk.services.dynamodb.model.WriteRequest;
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
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_BackupInUseException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_BackupNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ConditionalCheckFailedException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ContinuousBackupsUnavailableException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_DuplicateItemException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ExportConflictException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ExportNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_GlobalTableAlreadyExistsException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_GlobalTableNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_IdempotentParameterMismatchException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ImportConflictException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ImportNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_IndexNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_InternalServerError;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_InvalidExportTimeException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_InvalidRestoreTimeException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ItemCollectionSizeLimitExceededException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_LimitExceededException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_PointInTimeRecoveryUnavailableException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ProvisionedThroughputExceededException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ReplicaAlreadyExistsException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ReplicaNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_RequestLimitExceeded;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ResourceInUseException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_ResourceNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TableAlreadyExistsException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TableInUseException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TableNotFoundException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TransactionCanceledException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TransactionConflictException;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_TransactionInProgressException;
// BEGIN MANUAL EDIT
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error_Opaque;
// END MANUAL EDIT
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

public class ToNative {
  // BEGIN MANUAL EDIT
  public static RuntimeException Error(Error_Opaque dafnyValue) {
    if (dafnyValue.dtor_obj() instanceof DynamoDbException) {
      return (DynamoDbException) dafnyValue.dtor_obj();
    }
    // Because we only ever put `DynamoDbException` into `Error_Opaque`,
    // recieving any other type here indicates a bug with the codegen.
    // Bubble up some error to indicate this failure state.
    return new IllegalStateException("Unknown error recieved from DynamoDb.");
  }
  // END MANUAL EDIT

  public static ArchivalSummary ArchivalSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ArchivalSummary dafnyValue) {
    ArchivalSummary.Builder builder = ArchivalSummary.builder();
    if (dafnyValue.dtor_ArchivalBackupArn().is_Some()) {
      builder.archivalBackupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ArchivalBackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_ArchivalDateTime().is_Some()) {
      builder.archivalDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ArchivalDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_ArchivalReason().is_Some()) {
      builder.archivalReason(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ArchivalReason().dtor_value()));
    }
    return builder.build();
  }

  public static AttributeAction AttributeAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeAction dafnyValue) {
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

  public static AttributeDefinition AttributeDefinition(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeDefinition dafnyValue) {
    AttributeDefinition.Builder builder = AttributeDefinition.builder();
    builder.attributeName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    builder.attributeType(ToNative.ScalarAttributeType(dafnyValue.dtor_AttributeType()));
    return builder.build();
  }

  public static List<AttributeDefinition> AttributeDefinitions(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeDefinition> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeDefinition);
  }

  public static Map<String, AttributeValue> AttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static List<String> AttributeNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static Map<String, AttributeValueUpdate> AttributeUpdates(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValueUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValueUpdate);
  }

  public static AttributeValue AttributeValue(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue dafnyValue) {
    AttributeValue.Builder builder = AttributeValue.builder();
    if (dafnyValue.is_S()) {
      builder.s(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S()));
    }
    if (dafnyValue.is_N()) {
      builder.n(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_N()));
    }
    if (dafnyValue.is_B()) {
      builder.b(SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_B().toRawArray())));
    }
    if (dafnyValue.is_SS()) {
      builder.ss(ToNative.StringSetAttributeValue(dafnyValue.dtor_SS()));
    }
    if (dafnyValue.is_NS()) {
      builder.ns(ToNative.NumberSetAttributeValue(dafnyValue.dtor_NS()));
    }
    if (dafnyValue.is_BS()) {
      builder.bs(ToNative.BinarySetAttributeValue(dafnyValue.dtor_BS()));
    }
    if (dafnyValue.is_M()) {
      builder.m(ToNative.MapAttributeValue(dafnyValue.dtor_M()));
    }
    if (dafnyValue.is_L()) {
      builder.l(ToNative.ListAttributeValue(dafnyValue.dtor_L()));
    }
    if (dafnyValue.is_NULL()) {
      builder.nul((dafnyValue.dtor_NULL()));
    }
    if (dafnyValue.is_BOOL()) {
      builder.bool((dafnyValue.dtor_BOOL()));
    }
    return builder.build();
  }

  public static List<AttributeValue> AttributeValueList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static AttributeValueUpdate AttributeValueUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValueUpdate dafnyValue) {
    AttributeValueUpdate.Builder builder = AttributeValueUpdate.builder();
    if (dafnyValue.dtor_Action().is_Some()) {
      builder.action(ToNative.AttributeAction(dafnyValue.dtor_Action().dtor_value()));
    }
    if (dafnyValue.dtor_Value().is_Some()) {
      builder.value(ToNative.AttributeValue(dafnyValue.dtor_Value().dtor_value()));
    }
    return builder.build();
  }

  public static AutoScalingPolicyDescription AutoScalingPolicyDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingPolicyDescription dafnyValue) {
    AutoScalingPolicyDescription.Builder builder = AutoScalingPolicyDescription.builder();
    if (dafnyValue.dtor_PolicyName().is_Some()) {
      builder.policyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName().dtor_value()));
    }
    if (dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration().is_Some()) {
      builder.targetTrackingScalingPolicyConfiguration(ToNative.AutoScalingTargetTrackingScalingPolicyConfigurationDescription(dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration().dtor_value()));
    }
    return builder.build();
  }

  public static List<AutoScalingPolicyDescription> AutoScalingPolicyDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingPolicyDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AutoScalingPolicyDescription);
  }

  public static AutoScalingPolicyUpdate AutoScalingPolicyUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingPolicyUpdate dafnyValue) {
    AutoScalingPolicyUpdate.Builder builder = AutoScalingPolicyUpdate.builder();
    if (dafnyValue.dtor_PolicyName().is_Some()) {
      builder.policyName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_PolicyName().dtor_value()));
    }
    builder.targetTrackingScalingPolicyConfiguration(ToNative.AutoScalingTargetTrackingScalingPolicyConfigurationUpdate(dafnyValue.dtor_TargetTrackingScalingPolicyConfiguration()));
    return builder.build();
  }

  public static AutoScalingSettingsDescription AutoScalingSettingsDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingSettingsDescription dafnyValue) {
    AutoScalingSettingsDescription.Builder builder = AutoScalingSettingsDescription.builder();
    if (dafnyValue.dtor_AutoScalingDisabled().is_Some()) {
      builder.autoScalingDisabled((dafnyValue.dtor_AutoScalingDisabled().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingRoleArn().is_Some()) {
      builder.autoScalingRoleArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AutoScalingRoleArn().dtor_value()));
    }
    if (dafnyValue.dtor_MaximumUnits().is_Some()) {
      builder.maximumUnits((dafnyValue.dtor_MaximumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_MinimumUnits().is_Some()) {
      builder.minimumUnits((dafnyValue.dtor_MinimumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ScalingPolicies().is_Some()) {
      builder.scalingPolicies(ToNative.AutoScalingPolicyDescriptionList(dafnyValue.dtor_ScalingPolicies().dtor_value()));
    }
    return builder.build();
  }

  public static AutoScalingSettingsUpdate AutoScalingSettingsUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingSettingsUpdate dafnyValue) {
    AutoScalingSettingsUpdate.Builder builder = AutoScalingSettingsUpdate.builder();
    if (dafnyValue.dtor_AutoScalingDisabled().is_Some()) {
      builder.autoScalingDisabled((dafnyValue.dtor_AutoScalingDisabled().dtor_value()));
    }
    if (dafnyValue.dtor_AutoScalingRoleArn().is_Some()) {
      builder.autoScalingRoleArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AutoScalingRoleArn().dtor_value()));
    }
    if (dafnyValue.dtor_MaximumUnits().is_Some()) {
      builder.maximumUnits((dafnyValue.dtor_MaximumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_MinimumUnits().is_Some()) {
      builder.minimumUnits((dafnyValue.dtor_MinimumUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ScalingPolicyUpdate().is_Some()) {
      builder.scalingPolicyUpdate(ToNative.AutoScalingPolicyUpdate(dafnyValue.dtor_ScalingPolicyUpdate().dtor_value()));
    }
    return builder.build();
  }

  public static AutoScalingTargetTrackingScalingPolicyConfigurationDescription AutoScalingTargetTrackingScalingPolicyConfigurationDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingTargetTrackingScalingPolicyConfigurationDescription dafnyValue) {
    AutoScalingTargetTrackingScalingPolicyConfigurationDescription.Builder builder = AutoScalingTargetTrackingScalingPolicyConfigurationDescription.builder();
    if (dafnyValue.dtor_DisableScaleIn().is_Some()) {
      builder.disableScaleIn((dafnyValue.dtor_DisableScaleIn().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleInCooldown().is_Some()) {
      builder.scaleInCooldown((dafnyValue.dtor_ScaleInCooldown().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleOutCooldown().is_Some()) {
      builder.scaleOutCooldown((dafnyValue.dtor_ScaleOutCooldown().dtor_value()));
    }
    builder.targetValue(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_TargetValue()));
    return builder.build();
  }

  public static AutoScalingTargetTrackingScalingPolicyConfigurationUpdate AutoScalingTargetTrackingScalingPolicyConfigurationUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.AutoScalingTargetTrackingScalingPolicyConfigurationUpdate dafnyValue) {
    AutoScalingTargetTrackingScalingPolicyConfigurationUpdate.Builder builder = AutoScalingTargetTrackingScalingPolicyConfigurationUpdate.builder();
    if (dafnyValue.dtor_DisableScaleIn().is_Some()) {
      builder.disableScaleIn((dafnyValue.dtor_DisableScaleIn().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleInCooldown().is_Some()) {
      builder.scaleInCooldown((dafnyValue.dtor_ScaleInCooldown().dtor_value()));
    }
    if (dafnyValue.dtor_ScaleOutCooldown().is_Some()) {
      builder.scaleOutCooldown((dafnyValue.dtor_ScaleOutCooldown().dtor_value()));
    }
    builder.targetValue(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_TargetValue()));
    return builder.build();
  }

  public static BackupDescription BackupDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupDescription dafnyValue) {
    BackupDescription.Builder builder = BackupDescription.builder();
    if (dafnyValue.dtor_BackupDetails().is_Some()) {
      builder.backupDetails(ToNative.BackupDetails(dafnyValue.dtor_BackupDetails().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableDetails().is_Some()) {
      builder.sourceTableDetails(ToNative.SourceTableDetails(dafnyValue.dtor_SourceTableDetails().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableFeatureDetails().is_Some()) {
      builder.sourceTableFeatureDetails(ToNative.SourceTableFeatureDetails(dafnyValue.dtor_SourceTableFeatureDetails().dtor_value()));
    }
    return builder.build();
  }

  public static BackupDetails BackupDetails(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupDetails dafnyValue) {
    BackupDetails.Builder builder = BackupDetails.builder();
    builder.backupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    builder.backupCreationDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_BackupCreationDateTime()));
    if (dafnyValue.dtor_BackupExpiryDateTime().is_Some()) {
      builder.backupExpiryDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_BackupExpiryDateTime().dtor_value()));
    }
    builder.backupName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName()));
    if (dafnyValue.dtor_BackupSizeBytes().is_Some()) {
      builder.backupSizeBytes((dafnyValue.dtor_BackupSizeBytes().dtor_value()));
    }
    builder.backupStatus(ToNative.BackupStatus(dafnyValue.dtor_BackupStatus()));
    builder.backupType(ToNative.BackupType(dafnyValue.dtor_BackupType()));
    return builder.build();
  }

  public static BackupStatus BackupStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupStatus dafnyValue) {
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

  public static List<BackupSummary> BackupSummaries(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupSummary> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::BackupSummary);
  }

  public static BackupSummary BackupSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupSummary dafnyValue) {
    BackupSummary.Builder builder = BackupSummary.builder();
    if (dafnyValue.dtor_BackupArn().is_Some()) {
      builder.backupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_BackupCreationDateTime().is_Some()) {
      builder.backupCreationDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_BackupCreationDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_BackupExpiryDateTime().is_Some()) {
      builder.backupExpiryDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_BackupExpiryDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_BackupName().is_Some()) {
      builder.backupName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName().dtor_value()));
    }
    if (dafnyValue.dtor_BackupSizeBytes().is_Some()) {
      builder.backupSizeBytes((dafnyValue.dtor_BackupSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_BackupStatus().is_Some()) {
      builder.backupStatus(ToNative.BackupStatus(dafnyValue.dtor_BackupStatus().dtor_value()));
    }
    if (dafnyValue.dtor_BackupType().is_Some()) {
      builder.backupType(ToNative.BackupType(dafnyValue.dtor_BackupType().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      builder.tableId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static BackupType BackupType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupType dafnyValue) {
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

  public static BackupTypeFilter BackupTypeFilter(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BackupTypeFilter dafnyValue) {
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

  public static BatchExecuteStatementRequest BatchExecuteStatementInput(
      BatchExecuteStatementInput dafnyValue) {
    BatchExecuteStatementRequest.Builder builder = BatchExecuteStatementRequest.builder();
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    builder.statements(ToNative.PartiQLBatchRequest(dafnyValue.dtor_Statements()));
    return builder.build();
  }

  public static BatchExecuteStatementResponse BatchExecuteStatementOutput(
      BatchExecuteStatementOutput dafnyValue) {
    BatchExecuteStatementResponse.Builder builder = BatchExecuteStatementResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Responses().is_Some()) {
      builder.responses(ToNative.PartiQLBatchResponse(dafnyValue.dtor_Responses().dtor_value()));
    }
    return builder.build();
  }

  public static BatchGetItemRequest BatchGetItemInput(BatchGetItemInput dafnyValue) {
    BatchGetItemRequest.Builder builder = BatchGetItemRequest.builder();
    builder.requestItems(ToNative.BatchGetRequestMap(dafnyValue.dtor_RequestItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    return builder.build();
  }

  public static BatchGetItemResponse BatchGetItemOutput(BatchGetItemOutput dafnyValue) {
    BatchGetItemResponse.Builder builder = BatchGetItemResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Responses().is_Some()) {
      builder.responses(ToNative.BatchGetResponseMap(dafnyValue.dtor_Responses().dtor_value()));
    }
    if (dafnyValue.dtor_UnprocessedKeys().is_Some()) {
      builder.unprocessedKeys(ToNative.BatchGetRequestMap(dafnyValue.dtor_UnprocessedKeys().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, KeysAndAttributes> BatchGetRequestMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.KeysAndAttributes> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::KeysAndAttributes);
  }

  public static Map<String, List<Map<String, AttributeValue>>> BatchGetResponseMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue>>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ItemList);
  }

  public static BatchStatementError BatchStatementError(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementError dafnyValue) {
    BatchStatementError.Builder builder = BatchStatementError.builder();
    if (dafnyValue.dtor_Code().is_Some()) {
      builder.code(ToNative.BatchStatementErrorCodeEnum(dafnyValue.dtor_Code().dtor_value()));
    }
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return builder.build();
  }

  public static BatchStatementErrorCodeEnum BatchStatementErrorCodeEnum(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementErrorCodeEnum dafnyValue) {
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
    return BatchStatementErrorCodeEnum.fromValue(dafnyValue.toString());
  }

  public static BatchStatementRequest BatchStatementRequest(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementRequest dafnyValue) {
    BatchStatementRequest.Builder builder = BatchStatementRequest.builder();
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_Parameters().is_Some()) {
      builder.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    builder.statement(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    return builder.build();
  }

  public static BatchStatementResponse BatchStatementResponse(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementResponse dafnyValue) {
    BatchStatementResponse.Builder builder = BatchStatementResponse.builder();
    if (dafnyValue.dtor_Error().is_Some()) {
      builder.error(ToNative.BatchStatementError(dafnyValue.dtor_Error().dtor_value()));
    }
    if (dafnyValue.dtor_Item().is_Some()) {
      builder.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static BatchWriteItemRequest BatchWriteItemInput(BatchWriteItemInput dafnyValue) {
    BatchWriteItemRequest.Builder builder = BatchWriteItemRequest.builder();
    builder.requestItems(ToNative.BatchWriteItemRequestMap(dafnyValue.dtor_RequestItems()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      builder.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    return builder.build();
  }

  public static BatchWriteItemResponse BatchWriteItemOutput(BatchWriteItemOutput dafnyValue) {
    BatchWriteItemResponse.Builder builder = BatchWriteItemResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      builder.itemCollectionMetrics(ToNative.ItemCollectionMetricsPerTable(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_UnprocessedItems().is_Some()) {
      builder.unprocessedItems(ToNative.BatchWriteItemRequestMap(dafnyValue.dtor_UnprocessedItems().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, List<WriteRequest>> BatchWriteItemRequestMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.WriteRequest>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::WriteRequests);
  }

  public static BillingMode BillingMode(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BillingMode dafnyValue) {
    if (dafnyValue.is_PROVISIONED()) {
      return BillingMode.PROVISIONED;
    }
    if (dafnyValue.is_PAY__PER__REQUEST()) {
      return BillingMode.PAY_PER_REQUEST;
    }
    return BillingMode.fromValue(dafnyValue.toString());
  }

  public static BillingModeSummary BillingModeSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.BillingModeSummary dafnyValue) {
    BillingModeSummary.Builder builder = BillingModeSummary.builder();
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      builder.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdateToPayPerRequestDateTime().is_Some()) {
      builder.lastUpdateToPayPerRequestDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastUpdateToPayPerRequestDateTime().dtor_value()));
    }
    return builder.build();
  }

  public static List<SdkBytes> BinarySetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
        List<SdkBytes> returnList = new java.util.ArrayList<SdkBytes>();

        dafnyValue.forEach((value) -> {
            returnList.add(software.amazon.awssdk.core.SdkBytes.fromByteArray((byte[]) value.toRawArray()));
        });

        return returnList;
  }

  public static CancellationReason CancellationReason(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.CancellationReason dafnyValue) {
    CancellationReason.Builder builder = CancellationReason.builder();
    if (dafnyValue.dtor_Code().is_Some()) {
      builder.code(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Code().dtor_value()));
    }
    if (dafnyValue.dtor_Item().is_Some()) {
      builder.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return builder.build();
  }

  public static List<CancellationReason> CancellationReasonList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.CancellationReason> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::CancellationReason);
  }

  public static Capacity Capacity(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Capacity dafnyValue) {
    Capacity.Builder builder = Capacity.builder();
    if (dafnyValue.dtor_CapacityUnits().is_Some()) {
      builder.capacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_CapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      builder.readCapacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      builder.writeCapacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_WriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static ComparisonOperator ComparisonOperator(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator dafnyValue) {
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

  public static Condition Condition(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Condition dafnyValue) {
    Condition.Builder builder = Condition.builder();
    if (dafnyValue.dtor_AttributeValueList().is_Some()) {
      builder.attributeValueList(ToNative.AttributeValueList(dafnyValue.dtor_AttributeValueList().dtor_value()));
    }
    builder.comparisonOperator(ToNative.ComparisonOperator(dafnyValue.dtor_ComparisonOperator()));
    return builder.build();
  }

  public static ConditionalOperator ConditionalOperator(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ConditionalOperator dafnyValue) {
    if (dafnyValue.is_AND()) {
      return ConditionalOperator.AND;
    }
    if (dafnyValue.is_OR()) {
      return ConditionalOperator.OR;
    }
    return ConditionalOperator.fromValue(dafnyValue.toString());
  }

  public static ConditionCheck ConditionCheck(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ConditionCheck dafnyValue) {
    ConditionCheck.Builder builder = ConditionCheck.builder();
    builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression()));
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      builder.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static ConsumedCapacity ConsumedCapacity(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ConsumedCapacity dafnyValue) {
    ConsumedCapacity.Builder builder = ConsumedCapacity.builder();
    if (dafnyValue.dtor_CapacityUnits().is_Some()) {
      builder.capacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_CapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.SecondaryIndexesCapacityMap(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      builder.localSecondaryIndexes(ToNative.SecondaryIndexesCapacityMap(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      builder.readCapacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_Table().is_Some()) {
      builder.table(ToNative.Capacity(dafnyValue.dtor_Table().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      builder.writeCapacityUnits(software.amazon.smithy.dafny.conversion.ToNative.Simple.Double(dafnyValue.dtor_WriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static List<ConsumedCapacity> ConsumedCapacityMultiple(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ConsumedCapacity> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ConsumedCapacity);
  }

  public static ContinuousBackupsDescription ContinuousBackupsDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ContinuousBackupsDescription dafnyValue) {
    ContinuousBackupsDescription.Builder builder = ContinuousBackupsDescription.builder();
    builder.continuousBackupsStatus(ToNative.ContinuousBackupsStatus(dafnyValue.dtor_ContinuousBackupsStatus()));
    if (dafnyValue.dtor_PointInTimeRecoveryDescription().is_Some()) {
      builder.pointInTimeRecoveryDescription(ToNative.PointInTimeRecoveryDescription(dafnyValue.dtor_PointInTimeRecoveryDescription().dtor_value()));
    }
    return builder.build();
  }

  public static ContinuousBackupsStatus ContinuousBackupsStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ContinuousBackupsStatus dafnyValue) {
    if (dafnyValue.is_ENABLED()) {
      return ContinuousBackupsStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLED()) {
      return ContinuousBackupsStatus.DISABLED;
    }
    return ContinuousBackupsStatus.fromValue(dafnyValue.toString());
  }

  public static ContributorInsightsAction ContributorInsightsAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ContributorInsightsAction dafnyValue) {
    if (dafnyValue.is_ENABLE()) {
      return ContributorInsightsAction.ENABLE;
    }
    if (dafnyValue.is_DISABLE()) {
      return ContributorInsightsAction.DISABLE;
    }
    return ContributorInsightsAction.fromValue(dafnyValue.toString());
  }

  public static List<String> ContributorInsightsRuleList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static ContributorInsightsStatus ContributorInsightsStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ContributorInsightsStatus dafnyValue) {
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

  public static List<ContributorInsightsSummary> ContributorInsightsSummaries(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ContributorInsightsSummary> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ContributorInsightsSummary);
  }

  public static ContributorInsightsSummary ContributorInsightsSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ContributorInsightsSummary dafnyValue) {
    ContributorInsightsSummary.Builder builder = ContributorInsightsSummary.builder();
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      builder.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static CreateBackupRequest CreateBackupInput(CreateBackupInput dafnyValue) {
    CreateBackupRequest.Builder builder = CreateBackupRequest.builder();
    builder.backupName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupName()));
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static CreateBackupResponse CreateBackupOutput(CreateBackupOutput dafnyValue) {
    CreateBackupResponse.Builder builder = CreateBackupResponse.builder();
    if (dafnyValue.dtor_BackupDetails().is_Some()) {
      builder.backupDetails(ToNative.BackupDetails(dafnyValue.dtor_BackupDetails().dtor_value()));
    }
    return builder.build();
  }

  public static CreateGlobalSecondaryIndexAction CreateGlobalSecondaryIndexAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateGlobalSecondaryIndexAction dafnyValue) {
    CreateGlobalSecondaryIndexAction.Builder builder = CreateGlobalSecondaryIndexAction.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    builder.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return builder.build();
  }

  public static CreateGlobalTableRequest CreateGlobalTableInput(CreateGlobalTableInput dafnyValue) {
    CreateGlobalTableRequest.Builder builder = CreateGlobalTableRequest.builder();
    builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    builder.replicationGroup(ToNative.ReplicaList(dafnyValue.dtor_ReplicationGroup()));
    return builder.build();
  }

  public static CreateGlobalTableResponse CreateGlobalTableOutput(
      CreateGlobalTableOutput dafnyValue) {
    CreateGlobalTableResponse.Builder builder = CreateGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      builder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static CreateReplicaAction CreateReplicaAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateReplicaAction dafnyValue) {
    CreateReplicaAction.Builder builder = CreateReplicaAction.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return builder.build();
  }

  public static CreateReplicationGroupMemberAction CreateReplicationGroupMemberAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.CreateReplicationGroupMemberAction dafnyValue) {
    CreateReplicationGroupMemberAction.Builder builder = CreateReplicationGroupMemberAction.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      builder.kmsMasterKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_TableClassOverride().is_Some()) {
      builder.tableClassOverride(ToNative.TableClass(dafnyValue.dtor_TableClassOverride().dtor_value()));
    }
    return builder.build();
  }

  public static CreateTableRequest CreateTableInput(CreateTableInput dafnyValue) {
    CreateTableRequest.Builder builder = CreateTableRequest.builder();
    builder.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions()));
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      builder.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      builder.localSecondaryIndexes(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      builder.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      builder.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_TableClass().is_Some()) {
      builder.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return builder.build();
  }

  public static CreateTableResponse CreateTableOutput(CreateTableOutput dafnyValue) {
    CreateTableResponse.Builder builder = CreateTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      builder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static List<String> CsvHeaderList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static CsvOptions CsvOptions(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.CsvOptions dafnyValue) {
    CsvOptions.Builder builder = CsvOptions.builder();
    if (dafnyValue.dtor_Delimiter().is_Some()) {
      builder.delimiter(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Delimiter().dtor_value()));
    }
    if (dafnyValue.dtor_HeaderList().is_Some()) {
      builder.headerList(ToNative.CsvHeaderList(dafnyValue.dtor_HeaderList().dtor_value()));
    }
    return builder.build();
  }

  public static Delete Delete(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Delete dafnyValue) {
    Delete.Builder builder = Delete.builder();
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      builder.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DeleteBackupRequest DeleteBackupInput(DeleteBackupInput dafnyValue) {
    DeleteBackupRequest.Builder builder = DeleteBackupRequest.builder();
    builder.backupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    return builder.build();
  }

  public static DeleteBackupResponse DeleteBackupOutput(DeleteBackupOutput dafnyValue) {
    DeleteBackupResponse.Builder builder = DeleteBackupResponse.builder();
    if (dafnyValue.dtor_BackupDescription().is_Some()) {
      builder.backupDescription(ToNative.BackupDescription(dafnyValue.dtor_BackupDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DeleteGlobalSecondaryIndexAction DeleteGlobalSecondaryIndexAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteGlobalSecondaryIndexAction dafnyValue) {
    DeleteGlobalSecondaryIndexAction.Builder builder = DeleteGlobalSecondaryIndexAction.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    return builder.build();
  }

  public static DeleteItemRequest DeleteItemInput(DeleteItemInput dafnyValue) {
    DeleteItemRequest.Builder builder = DeleteItemRequest.builder();
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      builder.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_Expected().is_Some()) {
      builder.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      builder.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      builder.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DeleteItemResponse DeleteItemOutput(DeleteItemOutput dafnyValue) {
    DeleteItemResponse.Builder builder = DeleteItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      builder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      builder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return builder.build();
  }

  public static DeleteReplicaAction DeleteReplicaAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteReplicaAction dafnyValue) {
    DeleteReplicaAction.Builder builder = DeleteReplicaAction.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return builder.build();
  }

  public static DeleteReplicationGroupMemberAction DeleteReplicationGroupMemberAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteReplicationGroupMemberAction dafnyValue) {
    DeleteReplicationGroupMemberAction.Builder builder = DeleteReplicationGroupMemberAction.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    return builder.build();
  }

  public static DeleteRequest DeleteRequest(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteRequest dafnyValue) {
    DeleteRequest.Builder builder = DeleteRequest.builder();
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    return builder.build();
  }

  public static DeleteTableRequest DeleteTableInput(DeleteTableInput dafnyValue) {
    DeleteTableRequest.Builder builder = DeleteTableRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DeleteTableResponse DeleteTableOutput(DeleteTableOutput dafnyValue) {
    DeleteTableResponse.Builder builder = DeleteTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      builder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeBackupRequest DescribeBackupInput(DescribeBackupInput dafnyValue) {
    DescribeBackupRequest.Builder builder = DescribeBackupRequest.builder();
    builder.backupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    return builder.build();
  }

  public static DescribeBackupResponse DescribeBackupOutput(DescribeBackupOutput dafnyValue) {
    DescribeBackupResponse.Builder builder = DescribeBackupResponse.builder();
    if (dafnyValue.dtor_BackupDescription().is_Some()) {
      builder.backupDescription(ToNative.BackupDescription(dafnyValue.dtor_BackupDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeContinuousBackupsRequest DescribeContinuousBackupsInput(
      DescribeContinuousBackupsInput dafnyValue) {
    DescribeContinuousBackupsRequest.Builder builder = DescribeContinuousBackupsRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeContinuousBackupsResponse DescribeContinuousBackupsOutput(
      DescribeContinuousBackupsOutput dafnyValue) {
    DescribeContinuousBackupsResponse.Builder builder = DescribeContinuousBackupsResponse.builder();
    if (dafnyValue.dtor_ContinuousBackupsDescription().is_Some()) {
      builder.continuousBackupsDescription(ToNative.ContinuousBackupsDescription(dafnyValue.dtor_ContinuousBackupsDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeContributorInsightsRequest DescribeContributorInsightsInput(
      DescribeContributorInsightsInput dafnyValue) {
    DescribeContributorInsightsRequest.Builder builder = DescribeContributorInsightsRequest.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeContributorInsightsResponse DescribeContributorInsightsOutput(
      DescribeContributorInsightsOutput dafnyValue) {
    DescribeContributorInsightsResponse.Builder builder = DescribeContributorInsightsResponse.builder();
    if (dafnyValue.dtor_ContributorInsightsRuleList().is_Some()) {
      builder.contributorInsightsRuleList(ToNative.ContributorInsightsRuleList(dafnyValue.dtor_ContributorInsightsRuleList().dtor_value()));
    }
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      builder.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    if (dafnyValue.dtor_FailureException().is_Some()) {
      builder.failureException(ToNative.FailureException(dafnyValue.dtor_FailureException().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_LastUpdateDateTime().is_Some()) {
      builder.lastUpdateDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastUpdateDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeEndpointsRequest DescribeEndpointsRequest(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeEndpointsRequest dafnyValue) {
    return DescribeEndpointsRequest.builder().build();
  }

  public static DescribeEndpointsResponse DescribeEndpointsResponse(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DescribeEndpointsResponse dafnyValue) {
    DescribeEndpointsResponse.Builder builder = DescribeEndpointsResponse.builder();
    builder.endpoints(ToNative.Endpoints(dafnyValue.dtor_Endpoints()));
    return builder.build();
  }

  public static DescribeExportRequest DescribeExportInput(DescribeExportInput dafnyValue) {
    DescribeExportRequest.Builder builder = DescribeExportRequest.builder();
    builder.exportArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn()));
    return builder.build();
  }

  public static DescribeExportResponse DescribeExportOutput(DescribeExportOutput dafnyValue) {
    DescribeExportResponse.Builder builder = DescribeExportResponse.builder();
    if (dafnyValue.dtor_ExportDescription().is_Some()) {
      builder.exportDescription(ToNative.ExportDescription(dafnyValue.dtor_ExportDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeGlobalTableRequest DescribeGlobalTableInput(
      DescribeGlobalTableInput dafnyValue) {
    DescribeGlobalTableRequest.Builder builder = DescribeGlobalTableRequest.builder();
    builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    return builder.build();
  }

  public static DescribeGlobalTableResponse DescribeGlobalTableOutput(
      DescribeGlobalTableOutput dafnyValue) {
    DescribeGlobalTableResponse.Builder builder = DescribeGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      builder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeGlobalTableSettingsRequest DescribeGlobalTableSettingsInput(
      DescribeGlobalTableSettingsInput dafnyValue) {
    DescribeGlobalTableSettingsRequest.Builder builder = DescribeGlobalTableSettingsRequest.builder();
    builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    return builder.build();
  }

  public static DescribeGlobalTableSettingsResponse DescribeGlobalTableSettingsOutput(
      DescribeGlobalTableSettingsOutput dafnyValue) {
    DescribeGlobalTableSettingsResponse.Builder builder = DescribeGlobalTableSettingsResponse.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettings().is_Some()) {
      builder.replicaSettings(ToNative.ReplicaSettingsDescriptionList(dafnyValue.dtor_ReplicaSettings().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeImportRequest DescribeImportInput(DescribeImportInput dafnyValue) {
    DescribeImportRequest.Builder builder = DescribeImportRequest.builder();
    builder.importArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn()));
    return builder.build();
  }

  public static DescribeImportResponse DescribeImportOutput(DescribeImportOutput dafnyValue) {
    DescribeImportResponse.Builder builder = DescribeImportResponse.builder();
    builder.importTableDescription(ToNative.ImportTableDescription(dafnyValue.dtor_ImportTableDescription()));
    return builder.build();
  }

  public static DescribeKinesisStreamingDestinationRequest DescribeKinesisStreamingDestinationInput(
      DescribeKinesisStreamingDestinationInput dafnyValue) {
    DescribeKinesisStreamingDestinationRequest.Builder builder = DescribeKinesisStreamingDestinationRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeKinesisStreamingDestinationResponse DescribeKinesisStreamingDestinationOutput(
      DescribeKinesisStreamingDestinationOutput dafnyValue) {
    DescribeKinesisStreamingDestinationResponse.Builder builder = DescribeKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_KinesisDataStreamDestinations().is_Some()) {
      builder.kinesisDataStreamDestinations(ToNative.KinesisDataStreamDestinations(dafnyValue.dtor_KinesisDataStreamDestinations().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeLimitsRequest DescribeLimitsInput(DescribeLimitsInput dafnyValue) {
    return DescribeLimitsRequest.builder().build();
  }

  public static DescribeLimitsResponse DescribeLimitsOutput(DescribeLimitsOutput dafnyValue) {
    DescribeLimitsResponse.Builder builder = DescribeLimitsResponse.builder();
    if (dafnyValue.dtor_AccountMaxReadCapacityUnits().is_Some()) {
      builder.accountMaxReadCapacityUnits((dafnyValue.dtor_AccountMaxReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_AccountMaxWriteCapacityUnits().is_Some()) {
      builder.accountMaxWriteCapacityUnits((dafnyValue.dtor_AccountMaxWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_TableMaxReadCapacityUnits().is_Some()) {
      builder.tableMaxReadCapacityUnits((dafnyValue.dtor_TableMaxReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_TableMaxWriteCapacityUnits().is_Some()) {
      builder.tableMaxWriteCapacityUnits((dafnyValue.dtor_TableMaxWriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeTableRequest DescribeTableInput(DescribeTableInput dafnyValue) {
    DescribeTableRequest.Builder builder = DescribeTableRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeTableResponse DescribeTableOutput(DescribeTableOutput dafnyValue) {
    DescribeTableResponse.Builder builder = DescribeTableResponse.builder();
    if (dafnyValue.dtor_Table().is_Some()) {
      builder.table(ToNative.TableDescription(dafnyValue.dtor_Table().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeTableReplicaAutoScalingRequest DescribeTableReplicaAutoScalingInput(
      DescribeTableReplicaAutoScalingInput dafnyValue) {
    DescribeTableReplicaAutoScalingRequest.Builder builder = DescribeTableReplicaAutoScalingRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeTableReplicaAutoScalingResponse DescribeTableReplicaAutoScalingOutput(
      DescribeTableReplicaAutoScalingOutput dafnyValue) {
    DescribeTableReplicaAutoScalingResponse.Builder builder = DescribeTableReplicaAutoScalingResponse.builder();
    if (dafnyValue.dtor_TableAutoScalingDescription().is_Some()) {
      builder.tableAutoScalingDescription(ToNative.TableAutoScalingDescription(dafnyValue.dtor_TableAutoScalingDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DescribeTimeToLiveRequest DescribeTimeToLiveInput(
      DescribeTimeToLiveInput dafnyValue) {
    DescribeTimeToLiveRequest.Builder builder = DescribeTimeToLiveRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DescribeTimeToLiveResponse DescribeTimeToLiveOutput(
      DescribeTimeToLiveOutput dafnyValue) {
    DescribeTimeToLiveResponse.Builder builder = DescribeTimeToLiveResponse.builder();
    if (dafnyValue.dtor_TimeToLiveDescription().is_Some()) {
      builder.timeToLiveDescription(ToNative.TimeToLiveDescription(dafnyValue.dtor_TimeToLiveDescription().dtor_value()));
    }
    return builder.build();
  }

  public static DestinationStatus DestinationStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.DestinationStatus dafnyValue) {
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

  public static DisableKinesisStreamingDestinationRequest DisableKinesisStreamingDestinationInput(
      DisableKinesisStreamingDestinationInput dafnyValue) {
    DisableKinesisStreamingDestinationRequest.Builder builder = DisableKinesisStreamingDestinationRequest.builder();
    builder.streamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn()));
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static DisableKinesisStreamingDestinationResponse DisableKinesisStreamingDestinationOutput(
      DisableKinesisStreamingDestinationOutput dafnyValue) {
    DisableKinesisStreamingDestinationResponse.Builder builder = DisableKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      builder.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      builder.streamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static EnableKinesisStreamingDestinationRequest EnableKinesisStreamingDestinationInput(
      EnableKinesisStreamingDestinationInput dafnyValue) {
    EnableKinesisStreamingDestinationRequest.Builder builder = EnableKinesisStreamingDestinationRequest.builder();
    builder.streamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn()));
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static EnableKinesisStreamingDestinationResponse EnableKinesisStreamingDestinationOutput(
      EnableKinesisStreamingDestinationOutput dafnyValue) {
    EnableKinesisStreamingDestinationResponse.Builder builder = EnableKinesisStreamingDestinationResponse.builder();
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      builder.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      builder.streamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static Endpoint Endpoint(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Endpoint dafnyValue) {
    Endpoint.Builder builder = Endpoint.builder();
    builder.address(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Address()));
    builder.cachePeriodInMinutes((dafnyValue.dtor_CachePeriodInMinutes()));
    return builder.build();
  }

  public static List<Endpoint> Endpoints(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Endpoint> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Endpoint);
  }

  public static ExecuteStatementRequest ExecuteStatementInput(ExecuteStatementInput dafnyValue) {
    ExecuteStatementRequest.Builder builder = ExecuteStatementRequest.builder();
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_Parameters().is_Some()) {
      builder.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    builder.statement(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    return builder.build();
  }

  public static ExecuteStatementResponse ExecuteStatementOutput(ExecuteStatementOutput dafnyValue) {
    ExecuteStatementResponse.Builder builder = ExecuteStatementResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Items().is_Some()) {
      builder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      builder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return builder.build();
  }

  public static ExecuteTransactionRequest ExecuteTransactionInput(
      ExecuteTransactionInput dafnyValue) {
    ExecuteTransactionRequest.Builder builder = ExecuteTransactionRequest.builder();
    if (dafnyValue.dtor_ClientRequestToken().is_Some()) {
      builder.clientRequestToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientRequestToken().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    builder.transactStatements(ToNative.ParameterizedStatements(dafnyValue.dtor_TransactStatements()));
    return builder.build();
  }

  public static ExecuteTransactionResponse ExecuteTransactionOutput(
      ExecuteTransactionOutput dafnyValue) {
    ExecuteTransactionResponse.Builder builder = ExecuteTransactionResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Responses().is_Some()) {
      builder.responses(ToNative.ItemResponseList(dafnyValue.dtor_Responses().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, ExpectedAttributeValue> ExpectedAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ExpectedAttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ExpectedAttributeValue);
  }

  public static ExpectedAttributeValue ExpectedAttributeValue(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ExpectedAttributeValue dafnyValue) {
    ExpectedAttributeValue.Builder builder = ExpectedAttributeValue.builder();
    if (dafnyValue.dtor_AttributeValueList().is_Some()) {
      builder.attributeValueList(ToNative.AttributeValueList(dafnyValue.dtor_AttributeValueList().dtor_value()));
    }
    if (dafnyValue.dtor_ComparisonOperator().is_Some()) {
      builder.comparisonOperator(ToNative.ComparisonOperator(dafnyValue.dtor_ComparisonOperator().dtor_value()));
    }
    if (dafnyValue.dtor_Exists().is_Some()) {
      builder.exists((dafnyValue.dtor_Exists().dtor_value()));
    }
    if (dafnyValue.dtor_Value().is_Some()) {
      builder.value(ToNative.AttributeValue(dafnyValue.dtor_Value().dtor_value()));
    }
    return builder.build();
  }

  public static ExportDescription ExportDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportDescription dafnyValue) {
    ExportDescription.Builder builder = ExportDescription.builder();
    if (dafnyValue.dtor_BilledSizeBytes().is_Some()) {
      builder.billedSizeBytes((dafnyValue.dtor_BilledSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      builder.clientToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      builder.endTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_EndTime().dtor_value()));
    }
    if (dafnyValue.dtor_ExportArn().is_Some()) {
      builder.exportArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ExportFormat().is_Some()) {
      builder.exportFormat(ToNative.ExportFormat(dafnyValue.dtor_ExportFormat().dtor_value()));
    }
    if (dafnyValue.dtor_ExportManifest().is_Some()) {
      builder.exportManifest(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportManifest().dtor_value()));
    }
    if (dafnyValue.dtor_ExportStatus().is_Some()) {
      builder.exportStatus(ToNative.ExportStatus(dafnyValue.dtor_ExportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ExportTime().is_Some()) {
      builder.exportTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ExportTime().dtor_value()));
    }
    if (dafnyValue.dtor_FailureCode().is_Some()) {
      builder.failureCode(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureCode().dtor_value()));
    }
    if (dafnyValue.dtor_FailureMessage().is_Some()) {
      builder.failureMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureMessage().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      builder.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_S3Bucket().is_Some()) {
      builder.s3Bucket(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      builder.s3BucketOwner(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    if (dafnyValue.dtor_S3Prefix().is_Some()) {
      builder.s3Prefix(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Prefix().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseAlgorithm().is_Some()) {
      builder.s3SseAlgorithm(ToNative.S3SseAlgorithm(dafnyValue.dtor_S3SseAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseKmsKeyId().is_Some()) {
      builder.s3SseKmsKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3SseKmsKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      builder.startTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_StartTime().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      builder.tableId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    return builder.build();
  }

  public static ExportFormat ExportFormat(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportFormat dafnyValue) {
    if (dafnyValue.is_DYNAMODB__JSON()) {
      return ExportFormat.DYNAMODB_JSON;
    }
    if (dafnyValue.is_ION()) {
      return ExportFormat.ION;
    }
    return ExportFormat.fromValue(dafnyValue.toString());
  }

  public static ExportStatus ExportStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportStatus dafnyValue) {
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

  public static List<ExportSummary> ExportSummaries(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportSummary> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ExportSummary);
  }

  public static ExportSummary ExportSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ExportSummary dafnyValue) {
    ExportSummary.Builder builder = ExportSummary.builder();
    if (dafnyValue.dtor_ExportArn().is_Some()) {
      builder.exportArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ExportStatus().is_Some()) {
      builder.exportStatus(ToNative.ExportStatus(dafnyValue.dtor_ExportStatus().dtor_value()));
    }
    return builder.build();
  }

  public static ExportTableToPointInTimeRequest ExportTableToPointInTimeInput(
      ExportTableToPointInTimeInput dafnyValue) {
    ExportTableToPointInTimeRequest.Builder builder = ExportTableToPointInTimeRequest.builder();
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      builder.clientToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_ExportFormat().is_Some()) {
      builder.exportFormat(ToNative.ExportFormat(dafnyValue.dtor_ExportFormat().dtor_value()));
    }
    if (dafnyValue.dtor_ExportTime().is_Some()) {
      builder.exportTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ExportTime().dtor_value()));
    }
    builder.s3Bucket(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket()));
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      builder.s3BucketOwner(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    if (dafnyValue.dtor_S3Prefix().is_Some()) {
      builder.s3Prefix(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Prefix().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseAlgorithm().is_Some()) {
      builder.s3SseAlgorithm(ToNative.S3SseAlgorithm(dafnyValue.dtor_S3SseAlgorithm().dtor_value()));
    }
    if (dafnyValue.dtor_S3SseKmsKeyId().is_Some()) {
      builder.s3SseKmsKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3SseKmsKeyId().dtor_value()));
    }
    builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn()));
    return builder.build();
  }

  public static ExportTableToPointInTimeResponse ExportTableToPointInTimeOutput(
      ExportTableToPointInTimeOutput dafnyValue) {
    ExportTableToPointInTimeResponse.Builder builder = ExportTableToPointInTimeResponse.builder();
    if (dafnyValue.dtor_ExportDescription().is_Some()) {
      builder.exportDescription(ToNative.ExportDescription(dafnyValue.dtor_ExportDescription().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, String> ExpressionAttributeNameMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static Map<String, AttributeValue> ExpressionAttributeValueMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static FailureException FailureException(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.FailureException dafnyValue) {
    FailureException.Builder builder = FailureException.builder();
    if (dafnyValue.dtor_ExceptionDescription().is_Some()) {
      builder.exceptionDescription(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExceptionDescription().dtor_value()));
    }
    if (dafnyValue.dtor_ExceptionName().is_Some()) {
      builder.exceptionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExceptionName().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, Condition> FilterConditionMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Condition> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Condition);
  }

  public static Get Get(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Get dafnyValue) {
    Get.Builder builder = Get.builder();
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      builder.projectionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static GetItemRequest GetItemInput(GetItemInput dafnyValue) {
    GetItemRequest.Builder builder = GetItemRequest.builder();
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      builder.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      builder.projectionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static GetItemResponse GetItemOutput(GetItemOutput dafnyValue) {
    GetItemResponse.Builder builder = GetItemResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Item().is_Some()) {
      builder.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalSecondaryIndex GlobalSecondaryIndex(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndex dafnyValue) {
    GlobalSecondaryIndex.Builder builder = GlobalSecondaryIndex.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    builder.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalSecondaryIndexAutoScalingUpdate GlobalSecondaryIndexAutoScalingUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexAutoScalingUpdate dafnyValue) {
    GlobalSecondaryIndexAutoScalingUpdate.Builder builder = GlobalSecondaryIndexAutoScalingUpdate.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().is_Some()) {
      builder.provisionedWriteCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().dtor_value()));
    }
    return builder.build();
  }

  public static List<GlobalSecondaryIndexAutoScalingUpdate> GlobalSecondaryIndexAutoScalingUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexAutoScalingUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalSecondaryIndexAutoScalingUpdate);
  }

  public static GlobalSecondaryIndexDescription GlobalSecondaryIndexDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexDescription dafnyValue) {
    GlobalSecondaryIndexDescription.Builder builder = GlobalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_Backfilling().is_Some()) {
      builder.backfilling((dafnyValue.dtor_Backfilling().dtor_value()));
    }
    if (dafnyValue.dtor_IndexArn().is_Some()) {
      builder.indexArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexArn().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexSizeBytes().is_Some()) {
      builder.indexSizeBytes((dafnyValue.dtor_IndexSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      builder.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      builder.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      builder.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughputDescription(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return builder.build();
  }

  public static List<GlobalSecondaryIndexDescription> GlobalSecondaryIndexDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalSecondaryIndexDescription);
  }

  public static List<GlobalSecondaryIndexInfo> GlobalSecondaryIndexes(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexInfo> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalSecondaryIndexInfo);
  }

  public static GlobalSecondaryIndexInfo GlobalSecondaryIndexInfo(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexInfo dafnyValue) {
    GlobalSecondaryIndexInfo.Builder builder = GlobalSecondaryIndexInfo.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      builder.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    return builder.build();
  }

  public static List<GlobalSecondaryIndex> GlobalSecondaryIndexList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndex> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalSecondaryIndex);
  }

  public static GlobalSecondaryIndexUpdate GlobalSecondaryIndexUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexUpdate dafnyValue) {
    GlobalSecondaryIndexUpdate.Builder builder = GlobalSecondaryIndexUpdate.builder();
    if (dafnyValue.dtor_Create().is_Some()) {
      builder.create(ToNative.CreateGlobalSecondaryIndexAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      builder.delete(ToNative.DeleteGlobalSecondaryIndexAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    if (dafnyValue.dtor_Update().is_Some()) {
      builder.update(ToNative.UpdateGlobalSecondaryIndexAction(dafnyValue.dtor_Update().dtor_value()));
    }
    return builder.build();
  }

  public static List<GlobalSecondaryIndexUpdate> GlobalSecondaryIndexUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalSecondaryIndexUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalSecondaryIndexUpdate);
  }

  public static GlobalTable GlobalTable(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTable dafnyValue) {
    GlobalTable.Builder builder = GlobalTable.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicationGroup().is_Some()) {
      builder.replicationGroup(ToNative.ReplicaList(dafnyValue.dtor_ReplicationGroup().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalTableDescription GlobalTableDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTableDescription dafnyValue) {
    GlobalTableDescription.Builder builder = GlobalTableDescription.builder();
    if (dafnyValue.dtor_CreationDateTime().is_Some()) {
      builder.creationDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableArn().is_Some()) {
      builder.globalTableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableArn().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableStatus().is_Some()) {
      builder.globalTableStatus(ToNative.GlobalTableStatus(dafnyValue.dtor_GlobalTableStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicationGroup().is_Some()) {
      builder.replicationGroup(ToNative.ReplicaDescriptionList(dafnyValue.dtor_ReplicationGroup().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalTableGlobalSecondaryIndexSettingsUpdate GlobalTableGlobalSecondaryIndexSettingsUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTableGlobalSecondaryIndexSettingsUpdate dafnyValue) {
    GlobalTableGlobalSecondaryIndexSettingsUpdate.Builder builder = GlobalTableGlobalSecondaryIndexSettingsUpdate.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettingsUpdate().is_Some()) {
      builder.provisionedWriteCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityUnits().is_Some()) {
      builder.provisionedWriteCapacityUnits((dafnyValue.dtor_ProvisionedWriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static List<GlobalTableGlobalSecondaryIndexSettingsUpdate> GlobalTableGlobalSecondaryIndexSettingsUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTableGlobalSecondaryIndexSettingsUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalTableGlobalSecondaryIndexSettingsUpdate);
  }

  public static List<GlobalTable> GlobalTableList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTable> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::GlobalTable);
  }

  public static GlobalTableStatus GlobalTableStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.GlobalTableStatus dafnyValue) {
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

  public static ImportStatus ImportStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportStatus dafnyValue) {
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

  public static ImportSummary ImportSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportSummary dafnyValue) {
    ImportSummary.Builder builder = ImportSummary.builder();
    if (dafnyValue.dtor_CloudWatchLogGroupArn().is_Some()) {
      builder.cloudWatchLogGroupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudWatchLogGroupArn().dtor_value()));
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      builder.endTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_EndTime().dtor_value()));
    }
    if (dafnyValue.dtor_ImportArn().is_Some()) {
      builder.importArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ImportStatus().is_Some()) {
      builder.importStatus(ToNative.ImportStatus(dafnyValue.dtor_ImportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormat().is_Some()) {
      builder.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketSource().is_Some()) {
      builder.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      builder.startTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_StartTime().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    return builder.build();
  }

  public static List<ImportSummary> ImportSummaryList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportSummary> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ImportSummary);
  }

  public static ImportTableDescription ImportTableDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ImportTableDescription dafnyValue) {
    ImportTableDescription.Builder builder = ImportTableDescription.builder();
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      builder.clientToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_CloudWatchLogGroupArn().is_Some()) {
      builder.cloudWatchLogGroupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_CloudWatchLogGroupArn().dtor_value()));
    }
    if (dafnyValue.dtor_EndTime().is_Some()) {
      builder.endTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_EndTime().dtor_value()));
    }
    if (dafnyValue.dtor_ErrorCount().is_Some()) {
      builder.errorCount((dafnyValue.dtor_ErrorCount().dtor_value()));
    }
    if (dafnyValue.dtor_FailureCode().is_Some()) {
      builder.failureCode(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureCode().dtor_value()));
    }
    if (dafnyValue.dtor_FailureMessage().is_Some()) {
      builder.failureMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FailureMessage().dtor_value()));
    }
    if (dafnyValue.dtor_ImportArn().is_Some()) {
      builder.importArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ImportArn().dtor_value()));
    }
    if (dafnyValue.dtor_ImportedItemCount().is_Some()) {
      builder.importedItemCount((dafnyValue.dtor_ImportedItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_ImportStatus().is_Some()) {
      builder.importStatus(ToNative.ImportStatus(dafnyValue.dtor_ImportStatus().dtor_value()));
    }
    if (dafnyValue.dtor_InputCompressionType().is_Some()) {
      builder.inputCompressionType(ToNative.InputCompressionType(dafnyValue.dtor_InputCompressionType().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormat().is_Some()) {
      builder.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat().dtor_value()));
    }
    if (dafnyValue.dtor_InputFormatOptions().is_Some()) {
      builder.inputFormatOptions(ToNative.InputFormatOptions(dafnyValue.dtor_InputFormatOptions().dtor_value()));
    }
    if (dafnyValue.dtor_ProcessedItemCount().is_Some()) {
      builder.processedItemCount((dafnyValue.dtor_ProcessedItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_ProcessedSizeBytes().is_Some()) {
      builder.processedSizeBytes((dafnyValue.dtor_ProcessedSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_S3BucketSource().is_Some()) {
      builder.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource().dtor_value()));
    }
    if (dafnyValue.dtor_StartTime().is_Some()) {
      builder.startTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_StartTime().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableCreationParameters().is_Some()) {
      builder.tableCreationParameters(ToNative.TableCreationParameters(dafnyValue.dtor_TableCreationParameters().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      builder.tableId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    return builder.build();
  }

  public static ImportTableRequest ImportTableInput(ImportTableInput dafnyValue) {
    ImportTableRequest.Builder builder = ImportTableRequest.builder();
    if (dafnyValue.dtor_ClientToken().is_Some()) {
      builder.clientToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientToken().dtor_value()));
    }
    if (dafnyValue.dtor_InputCompressionType().is_Some()) {
      builder.inputCompressionType(ToNative.InputCompressionType(dafnyValue.dtor_InputCompressionType().dtor_value()));
    }
    builder.inputFormat(ToNative.InputFormat(dafnyValue.dtor_InputFormat()));
    if (dafnyValue.dtor_InputFormatOptions().is_Some()) {
      builder.inputFormatOptions(ToNative.InputFormatOptions(dafnyValue.dtor_InputFormatOptions().dtor_value()));
    }
    builder.s3BucketSource(ToNative.S3BucketSource(dafnyValue.dtor_S3BucketSource()));
    builder.tableCreationParameters(ToNative.TableCreationParameters(dafnyValue.dtor_TableCreationParameters()));
    return builder.build();
  }

  public static ImportTableResponse ImportTableOutput(ImportTableOutput dafnyValue) {
    ImportTableResponse.Builder builder = ImportTableResponse.builder();
    builder.importTableDescription(ToNative.ImportTableDescription(dafnyValue.dtor_ImportTableDescription()));
    return builder.build();
  }

  public static IndexStatus IndexStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IndexStatus dafnyValue) {
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

  public static InputCompressionType InputCompressionType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.InputCompressionType dafnyValue) {
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

  public static InputFormat InputFormat(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.InputFormat dafnyValue) {
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
      software.amazon.cryptography.services.dynamodb.internaldafny.types.InputFormatOptions dafnyValue) {
    InputFormatOptions.Builder builder = InputFormatOptions.builder();
    if (dafnyValue.dtor_Csv().is_Some()) {
      builder.csv(ToNative.CsvOptions(dafnyValue.dtor_Csv().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, AttributeValue> ItemCollectionKeyAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static ItemCollectionMetrics ItemCollectionMetrics(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemCollectionMetrics dafnyValue) {
    ItemCollectionMetrics.Builder builder = ItemCollectionMetrics.builder();
    if (dafnyValue.dtor_ItemCollectionKey().is_Some()) {
      builder.itemCollectionKey(ToNative.ItemCollectionKeyAttributeMap(dafnyValue.dtor_ItemCollectionKey().dtor_value()));
    }
    if (dafnyValue.dtor_SizeEstimateRangeGB().is_Some()) {
      builder.sizeEstimateRangeGB(ToNative.ItemCollectionSizeEstimateRange(dafnyValue.dtor_SizeEstimateRangeGB().dtor_value()));
    }
    return builder.build();
  }

  public static List<ItemCollectionMetrics> ItemCollectionMetricsMultiple(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemCollectionMetrics> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ItemCollectionMetrics);
  }

  public static Map<String, List<ItemCollectionMetrics>> ItemCollectionMetricsPerTable(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemCollectionMetrics>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ItemCollectionMetricsMultiple);
  }

  public static List<Double> ItemCollectionSizeEstimateRange(
      DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::Double);
  }

  public static List<Map<String, AttributeValue>> ItemList(
      DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeMap);
  }

  public static ItemResponse ItemResponse(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemResponse dafnyValue) {
    ItemResponse.Builder builder = ItemResponse.builder();
    if (dafnyValue.dtor_Item().is_Some()) {
      builder.item(ToNative.AttributeMap(dafnyValue.dtor_Item().dtor_value()));
    }
    return builder.build();
  }

  public static List<ItemResponse> ItemResponseList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemResponse> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ItemResponse);
  }

  public static Map<String, AttributeValue> Key(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static Map<String, Condition> KeyConditions(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Condition> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Condition);
  }

  public static List<Map<String, AttributeValue>> KeyList(
      DafnySequence<? extends DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Key);
  }

  public static KeysAndAttributes KeysAndAttributes(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.KeysAndAttributes dafnyValue) {
    KeysAndAttributes.Builder builder = KeysAndAttributes.builder();
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      builder.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    builder.keys(ToNative.KeyList(dafnyValue.dtor_Keys()));
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      builder.projectionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    return builder.build();
  }

  public static List<KeySchemaElement> KeySchema(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.KeySchemaElement> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::KeySchemaElement);
  }

  public static KeySchemaElement KeySchemaElement(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.KeySchemaElement dafnyValue) {
    KeySchemaElement.Builder builder = KeySchemaElement.builder();
    builder.attributeName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    builder.keyType(ToNative.KeyType(dafnyValue.dtor_KeyType()));
    return builder.build();
  }

  public static KeyType KeyType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.KeyType dafnyValue) {
    if (dafnyValue.is_HASH()) {
      return KeyType.HASH;
    }
    if (dafnyValue.is_RANGE()) {
      return KeyType.RANGE;
    }
    return KeyType.fromValue(dafnyValue.toString());
  }

  public static KinesisDataStreamDestination KinesisDataStreamDestination(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.KinesisDataStreamDestination dafnyValue) {
    KinesisDataStreamDestination.Builder builder = KinesisDataStreamDestination.builder();
    if (dafnyValue.dtor_DestinationStatus().is_Some()) {
      builder.destinationStatus(ToNative.DestinationStatus(dafnyValue.dtor_DestinationStatus().dtor_value()));
    }
    if (dafnyValue.dtor_DestinationStatusDescription().is_Some()) {
      builder.destinationStatusDescription(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_DestinationStatusDescription().dtor_value()));
    }
    if (dafnyValue.dtor_StreamArn().is_Some()) {
      builder.streamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_StreamArn().dtor_value()));
    }
    return builder.build();
  }

  public static List<KinesisDataStreamDestination> KinesisDataStreamDestinations(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.KinesisDataStreamDestination> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::KinesisDataStreamDestination);
  }

  public static List<AttributeValue> ListAttributeValue(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static ListBackupsRequest ListBackupsInput(ListBackupsInput dafnyValue) {
    ListBackupsRequest.Builder builder = ListBackupsRequest.builder();
    if (dafnyValue.dtor_BackupType().is_Some()) {
      builder.backupType(ToNative.BackupTypeFilter(dafnyValue.dtor_BackupType().dtor_value()));
    }
    if (dafnyValue.dtor_ExclusiveStartBackupArn().is_Some()) {
      builder.exclusiveStartBackupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartBackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_TimeRangeLowerBound().is_Some()) {
      builder.timeRangeLowerBound(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_TimeRangeLowerBound().dtor_value()));
    }
    if (dafnyValue.dtor_TimeRangeUpperBound().is_Some()) {
      builder.timeRangeUpperBound(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_TimeRangeUpperBound().dtor_value()));
    }
    return builder.build();
  }

  public static ListBackupsResponse ListBackupsOutput(ListBackupsOutput dafnyValue) {
    ListBackupsResponse.Builder builder = ListBackupsResponse.builder();
    if (dafnyValue.dtor_BackupSummaries().is_Some()) {
      builder.backupSummaries(ToNative.BackupSummaries(dafnyValue.dtor_BackupSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedBackupArn().is_Some()) {
      builder.lastEvaluatedBackupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedBackupArn().dtor_value()));
    }
    return builder.build();
  }

  public static ListContributorInsightsRequest ListContributorInsightsInput(
      ListContributorInsightsInput dafnyValue) {
    ListContributorInsightsRequest.Builder builder = ListContributorInsightsRequest.builder();
    if (dafnyValue.dtor_MaxResults().is_Some()) {
      builder.maxResults((dafnyValue.dtor_MaxResults().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static ListContributorInsightsResponse ListContributorInsightsOutput(
      ListContributorInsightsOutput dafnyValue) {
    ListContributorInsightsResponse.Builder builder = ListContributorInsightsResponse.builder();
    if (dafnyValue.dtor_ContributorInsightsSummaries().is_Some()) {
      builder.contributorInsightsSummaries(ToNative.ContributorInsightsSummaries(dafnyValue.dtor_ContributorInsightsSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return builder.build();
  }

  public static ListExportsRequest ListExportsInput(ListExportsInput dafnyValue) {
    ListExportsRequest.Builder builder = ListExportsRequest.builder();
    if (dafnyValue.dtor_MaxResults().is_Some()) {
      builder.maxResults((dafnyValue.dtor_MaxResults().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    return builder.build();
  }

  public static ListExportsResponse ListExportsOutput(ListExportsOutput dafnyValue) {
    ListExportsResponse.Builder builder = ListExportsResponse.builder();
    if (dafnyValue.dtor_ExportSummaries().is_Some()) {
      builder.exportSummaries(ToNative.ExportSummaries(dafnyValue.dtor_ExportSummaries().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return builder.build();
  }

  public static ListGlobalTablesRequest ListGlobalTablesInput(ListGlobalTablesInput dafnyValue) {
    ListGlobalTablesRequest.Builder builder = ListGlobalTablesRequest.builder();
    if (dafnyValue.dtor_ExclusiveStartGlobalTableName().is_Some()) {
      builder.exclusiveStartGlobalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartGlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_RegionName().is_Some()) {
      builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    return builder.build();
  }

  public static ListGlobalTablesResponse ListGlobalTablesOutput(ListGlobalTablesOutput dafnyValue) {
    ListGlobalTablesResponse.Builder builder = ListGlobalTablesResponse.builder();
    if (dafnyValue.dtor_GlobalTables().is_Some()) {
      builder.globalTables(ToNative.GlobalTableList(dafnyValue.dtor_GlobalTables().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedGlobalTableName().is_Some()) {
      builder.lastEvaluatedGlobalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedGlobalTableName().dtor_value()));
    }
    return builder.build();
  }

  public static ListImportsRequest ListImportsInput(ListImportsInput dafnyValue) {
    ListImportsRequest.Builder builder = ListImportsRequest.builder();
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_PageSize().is_Some()) {
      builder.pageSize((dafnyValue.dtor_PageSize().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    return builder.build();
  }

  public static ListImportsResponse ListImportsOutput(ListImportsOutput dafnyValue) {
    ListImportsResponse.Builder builder = ListImportsResponse.builder();
    if (dafnyValue.dtor_ImportSummaryList().is_Some()) {
      builder.importSummaryList(ToNative.ImportSummaryList(dafnyValue.dtor_ImportSummaryList().dtor_value()));
    }
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    return builder.build();
  }

  public static ListTablesRequest ListTablesInput(ListTablesInput dafnyValue) {
    ListTablesRequest.Builder builder = ListTablesRequest.builder();
    if (dafnyValue.dtor_ExclusiveStartTableName().is_Some()) {
      builder.exclusiveStartTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ExclusiveStartTableName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    return builder.build();
  }

  public static ListTablesResponse ListTablesOutput(ListTablesOutput dafnyValue) {
    ListTablesResponse.Builder builder = ListTablesResponse.builder();
    if (dafnyValue.dtor_LastEvaluatedTableName().is_Some()) {
      builder.lastEvaluatedTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LastEvaluatedTableName().dtor_value()));
    }
    if (dafnyValue.dtor_TableNames().is_Some()) {
      builder.tableNames(ToNative.TableNameList(dafnyValue.dtor_TableNames().dtor_value()));
    }
    return builder.build();
  }

  public static ListTagsOfResourceRequest ListTagsOfResourceInput(
      ListTagsOfResourceInput dafnyValue) {
    ListTagsOfResourceRequest.Builder builder = ListTagsOfResourceRequest.builder();
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    builder.resourceArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    return builder.build();
  }

  public static ListTagsOfResourceResponse ListTagsOfResourceOutput(
      ListTagsOfResourceOutput dafnyValue) {
    ListTagsOfResourceResponse.Builder builder = ListTagsOfResourceResponse.builder();
    if (dafnyValue.dtor_NextToken().is_Some()) {
      builder.nextToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_NextToken().dtor_value()));
    }
    if (dafnyValue.dtor_Tags().is_Some()) {
      builder.tags(ToNative.TagList(dafnyValue.dtor_Tags().dtor_value()));
    }
    return builder.build();
  }

  public static LocalSecondaryIndex LocalSecondaryIndex(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndex dafnyValue) {
    LocalSecondaryIndex.Builder builder = LocalSecondaryIndex.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    builder.projection(ToNative.Projection(dafnyValue.dtor_Projection()));
    return builder.build();
  }

  public static LocalSecondaryIndexDescription LocalSecondaryIndexDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndexDescription dafnyValue) {
    LocalSecondaryIndexDescription.Builder builder = LocalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_IndexArn().is_Some()) {
      builder.indexArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexArn().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexSizeBytes().is_Some()) {
      builder.indexSizeBytes((dafnyValue.dtor_IndexSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      builder.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      builder.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    return builder.build();
  }

  public static List<LocalSecondaryIndexDescription> LocalSecondaryIndexDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::LocalSecondaryIndexDescription);
  }

  public static List<LocalSecondaryIndexInfo> LocalSecondaryIndexes(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndexInfo> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::LocalSecondaryIndexInfo);
  }

  public static LocalSecondaryIndexInfo LocalSecondaryIndexInfo(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndexInfo dafnyValue) {
    LocalSecondaryIndexInfo.Builder builder = LocalSecondaryIndexInfo.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_Projection().is_Some()) {
      builder.projection(ToNative.Projection(dafnyValue.dtor_Projection().dtor_value()));
    }
    return builder.build();
  }

  public static List<LocalSecondaryIndex> LocalSecondaryIndexList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.LocalSecondaryIndex> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::LocalSecondaryIndex);
  }

  public static Map<String, AttributeValue> MapAttributeValue(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static List<String> NonKeyAttributeNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<String> NumberSetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static ParameterizedStatement ParameterizedStatement(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ParameterizedStatement dafnyValue) {
    ParameterizedStatement.Builder builder = ParameterizedStatement.builder();
    if (dafnyValue.dtor_Parameters().is_Some()) {
      builder.parameters(ToNative.PreparedStatementParameters(dafnyValue.dtor_Parameters().dtor_value()));
    }
    builder.statement(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Statement()));
    return builder.build();
  }

  public static List<ParameterizedStatement> ParameterizedStatements(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ParameterizedStatement> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ParameterizedStatement);
  }

  public static List<BatchStatementRequest> PartiQLBatchRequest(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementRequest> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::BatchStatementRequest);
  }

  public static List<BatchStatementResponse> PartiQLBatchResponse(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementResponse> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::BatchStatementResponse);
  }

  public static PointInTimeRecoveryDescription PointInTimeRecoveryDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.PointInTimeRecoveryDescription dafnyValue) {
    PointInTimeRecoveryDescription.Builder builder = PointInTimeRecoveryDescription.builder();
    if (dafnyValue.dtor_EarliestRestorableDateTime().is_Some()) {
      builder.earliestRestorableDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_EarliestRestorableDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_LatestRestorableDateTime().is_Some()) {
      builder.latestRestorableDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LatestRestorableDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_PointInTimeRecoveryStatus().is_Some()) {
      builder.pointInTimeRecoveryStatus(ToNative.PointInTimeRecoveryStatus(dafnyValue.dtor_PointInTimeRecoveryStatus().dtor_value()));
    }
    return builder.build();
  }

  public static PointInTimeRecoverySpecification PointInTimeRecoverySpecification(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.PointInTimeRecoverySpecification dafnyValue) {
    PointInTimeRecoverySpecification.Builder builder = PointInTimeRecoverySpecification.builder();
    builder.pointInTimeRecoveryEnabled((dafnyValue.dtor_PointInTimeRecoveryEnabled()));
    return builder.build();
  }

  public static PointInTimeRecoveryStatus PointInTimeRecoveryStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.PointInTimeRecoveryStatus dafnyValue) {
    if (dafnyValue.is_ENABLED()) {
      return PointInTimeRecoveryStatus.ENABLED;
    }
    if (dafnyValue.is_DISABLED()) {
      return PointInTimeRecoveryStatus.DISABLED;
    }
    return PointInTimeRecoveryStatus.fromValue(dafnyValue.toString());
  }

  public static List<AttributeValue> PreparedStatementParameters(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static Projection Projection(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Projection dafnyValue) {
    Projection.Builder builder = Projection.builder();
    if (dafnyValue.dtor_NonKeyAttributes().is_Some()) {
      builder.nonKeyAttributes(ToNative.NonKeyAttributeNameList(dafnyValue.dtor_NonKeyAttributes().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionType().is_Some()) {
      builder.projectionType(ToNative.ProjectionType(dafnyValue.dtor_ProjectionType().dtor_value()));
    }
    return builder.build();
  }

  public static ProjectionType ProjectionType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ProjectionType dafnyValue) {
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

  public static ProvisionedThroughput ProvisionedThroughput(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ProvisionedThroughput dafnyValue) {
    ProvisionedThroughput.Builder builder = ProvisionedThroughput.builder();
    builder.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits()));
    builder.writeCapacityUnits((dafnyValue.dtor_WriteCapacityUnits()));
    return builder.build();
  }

  public static ProvisionedThroughputDescription ProvisionedThroughputDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ProvisionedThroughputDescription dafnyValue) {
    ProvisionedThroughputDescription.Builder builder = ProvisionedThroughputDescription.builder();
    if (dafnyValue.dtor_LastDecreaseDateTime().is_Some()) {
      builder.lastDecreaseDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastDecreaseDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_LastIncreaseDateTime().is_Some()) {
      builder.lastIncreaseDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastIncreaseDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_NumberOfDecreasesToday().is_Some()) {
      builder.numberOfDecreasesToday((dafnyValue.dtor_NumberOfDecreasesToday().dtor_value()));
    }
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      builder.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_WriteCapacityUnits().is_Some()) {
      builder.writeCapacityUnits((dafnyValue.dtor_WriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static ProvisionedThroughputOverride ProvisionedThroughputOverride(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ProvisionedThroughputOverride dafnyValue) {
    ProvisionedThroughputOverride.Builder builder = ProvisionedThroughputOverride.builder();
    if (dafnyValue.dtor_ReadCapacityUnits().is_Some()) {
      builder.readCapacityUnits((dafnyValue.dtor_ReadCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static Put Put(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Put dafnyValue) {
    Put.Builder builder = Put.builder();
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      builder.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static PutItemRequest PutItemInput(PutItemInput dafnyValue) {
    PutItemRequest.Builder builder = PutItemRequest.builder();
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      builder.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_Expected().is_Some()) {
      builder.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      builder.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      builder.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static Map<String, AttributeValue> PutItemInputAttributeMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::AttributeValue);
  }

  public static PutItemResponse PutItemOutput(PutItemOutput dafnyValue) {
    PutItemResponse.Builder builder = PutItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      builder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      builder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return builder.build();
  }

  public static PutRequest PutRequest(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.PutRequest dafnyValue) {
    PutRequest.Builder builder = PutRequest.builder();
    builder.item(ToNative.PutItemInputAttributeMap(dafnyValue.dtor_Item()));
    return builder.build();
  }

  public static QueryRequest QueryInput(QueryInput dafnyValue) {
    QueryRequest.Builder builder = QueryRequest.builder();
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      builder.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      builder.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ExclusiveStartKey().is_Some()) {
      builder.exclusiveStartKey(ToNative.Key(dafnyValue.dtor_ExclusiveStartKey().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_FilterExpression().is_Some()) {
      builder.filterExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FilterExpression().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_KeyConditionExpression().is_Some()) {
      builder.keyConditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KeyConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_KeyConditions().is_Some()) {
      builder.keyConditions(ToNative.KeyConditions(dafnyValue.dtor_KeyConditions().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      builder.projectionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_QueryFilter().is_Some()) {
      builder.queryFilter(ToNative.FilterConditionMap(dafnyValue.dtor_QueryFilter().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ScanIndexForward().is_Some()) {
      builder.scanIndexForward((dafnyValue.dtor_ScanIndexForward().dtor_value()));
    }
    if (dafnyValue.dtor_Select().is_Some()) {
      builder.select(ToNative.Select(dafnyValue.dtor_Select().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static QueryResponse QueryOutput(QueryOutput dafnyValue) {
    QueryResponse.Builder builder = QueryResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Count().is_Some()) {
      builder.count((dafnyValue.dtor_Count().dtor_value()));
    }
    if (dafnyValue.dtor_Items().is_Some()) {
      builder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      builder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    if (dafnyValue.dtor_ScannedCount().is_Some()) {
      builder.scannedCount((dafnyValue.dtor_ScannedCount().dtor_value()));
    }
    return builder.build();
  }

  public static Replica Replica(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Replica dafnyValue) {
    Replica.Builder builder = Replica.builder();
    if (dafnyValue.dtor_RegionName().is_Some()) {
      builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicaAutoScalingDescription ReplicaAutoScalingDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaAutoScalingDescription dafnyValue) {
    ReplicaAutoScalingDescription.Builder builder = ReplicaAutoScalingDescription.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexAutoScalingDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_RegionName().is_Some()) {
      builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      builder.replicaProvisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      builder.replicaProvisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      builder.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaAutoScalingDescription> ReplicaAutoScalingDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaAutoScalingDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaAutoScalingDescription);
  }

  public static ReplicaAutoScalingUpdate ReplicaAutoScalingUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaAutoScalingUpdate dafnyValue) {
    ReplicaAutoScalingUpdate.Builder builder = ReplicaAutoScalingUpdate.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexUpdates().is_Some()) {
      builder.replicaGlobalSecondaryIndexUpdates(ToNative.ReplicaGlobalSecondaryIndexAutoScalingUpdateList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingUpdate().is_Some()) {
      builder.replicaProvisionedReadCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingUpdate().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaAutoScalingUpdate> ReplicaAutoScalingUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaAutoScalingUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaAutoScalingUpdate);
  }

  public static ReplicaDescription ReplicaDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaDescription dafnyValue) {
    ReplicaDescription.Builder builder = ReplicaDescription.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      builder.kmsMasterKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_RegionName().is_Some()) {
      builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaInaccessibleDateTime().is_Some()) {
      builder.replicaInaccessibleDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_ReplicaInaccessibleDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      builder.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatusDescription().is_Some()) {
      builder.replicaStatusDescription(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaStatusDescription().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatusPercentProgress().is_Some()) {
      builder.replicaStatusPercentProgress(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ReplicaStatusPercentProgress().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTableClassSummary().is_Some()) {
      builder.replicaTableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_ReplicaTableClassSummary().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaDescription> ReplicaDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaDescription);
  }

  public static ReplicaGlobalSecondaryIndex ReplicaGlobalSecondaryIndex(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndex dafnyValue) {
    ReplicaGlobalSecondaryIndex.Builder builder = ReplicaGlobalSecondaryIndex.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicaGlobalSecondaryIndexAutoScalingDescription ReplicaGlobalSecondaryIndexAutoScalingDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexAutoScalingDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexAutoScalingDescription.Builder builder = ReplicaGlobalSecondaryIndexAutoScalingDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      builder.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      builder.provisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      builder.provisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaGlobalSecondaryIndexAutoScalingDescription> ReplicaGlobalSecondaryIndexAutoScalingDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexAutoScalingDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndexAutoScalingDescription);
  }

  public static ReplicaGlobalSecondaryIndexAutoScalingUpdate ReplicaGlobalSecondaryIndexAutoScalingUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexAutoScalingUpdate dafnyValue) {
    ReplicaGlobalSecondaryIndexAutoScalingUpdate.Builder builder = ReplicaGlobalSecondaryIndexAutoScalingUpdate.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingUpdate().is_Some()) {
      builder.provisionedReadCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingUpdate().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaGlobalSecondaryIndexAutoScalingUpdate> ReplicaGlobalSecondaryIndexAutoScalingUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexAutoScalingUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndexAutoScalingUpdate);
  }

  public static ReplicaGlobalSecondaryIndexDescription ReplicaGlobalSecondaryIndexDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexDescription.Builder builder = ReplicaGlobalSecondaryIndexDescription.builder();
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaGlobalSecondaryIndexDescription> ReplicaGlobalSecondaryIndexDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndexDescription);
  }

  public static List<ReplicaGlobalSecondaryIndex> ReplicaGlobalSecondaryIndexList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndex> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndex);
  }

  public static ReplicaGlobalSecondaryIndexSettingsDescription ReplicaGlobalSecondaryIndexSettingsDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexSettingsDescription dafnyValue) {
    ReplicaGlobalSecondaryIndexSettingsDescription.Builder builder = ReplicaGlobalSecondaryIndexSettingsDescription.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_IndexStatus().is_Some()) {
      builder.indexStatus(ToNative.IndexStatus(dafnyValue.dtor_IndexStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      builder.provisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityUnits().is_Some()) {
      builder.provisionedReadCapacityUnits((dafnyValue.dtor_ProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      builder.provisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityUnits().is_Some()) {
      builder.provisionedWriteCapacityUnits((dafnyValue.dtor_ProvisionedWriteCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaGlobalSecondaryIndexSettingsDescription> ReplicaGlobalSecondaryIndexSettingsDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexSettingsDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndexSettingsDescription);
  }

  public static ReplicaGlobalSecondaryIndexSettingsUpdate ReplicaGlobalSecondaryIndexSettingsUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexSettingsUpdate dafnyValue) {
    ReplicaGlobalSecondaryIndexSettingsUpdate.Builder builder = ReplicaGlobalSecondaryIndexSettingsUpdate.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    if (dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettingsUpdate().is_Some()) {
      builder.provisionedReadCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedReadCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedReadCapacityUnits().is_Some()) {
      builder.provisionedReadCapacityUnits((dafnyValue.dtor_ProvisionedReadCapacityUnits().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaGlobalSecondaryIndexSettingsUpdate> ReplicaGlobalSecondaryIndexSettingsUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaGlobalSecondaryIndexSettingsUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaGlobalSecondaryIndexSettingsUpdate);
  }

  public static List<Replica> ReplicaList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Replica> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Replica);
  }

  public static ReplicaSettingsDescription ReplicaSettingsDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaSettingsDescription dafnyValue) {
    ReplicaSettingsDescription.Builder builder = ReplicaSettingsDescription.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaBillingModeSummary().is_Some()) {
      builder.replicaBillingModeSummary(ToNative.BillingModeSummary(dafnyValue.dtor_ReplicaBillingModeSummary().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettings().is_Some()) {
      builder.replicaGlobalSecondaryIndexSettings(ToNative.ReplicaGlobalSecondaryIndexSettingsDescriptionList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().is_Some()) {
      builder.replicaProvisionedReadCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().is_Some()) {
      builder.replicaProvisionedReadCapacityUnits((dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().is_Some()) {
      builder.replicaProvisionedWriteCapacityAutoScalingSettings(ToNative.AutoScalingSettingsDescription(dafnyValue.dtor_ReplicaProvisionedWriteCapacityAutoScalingSettings().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedWriteCapacityUnits().is_Some()) {
      builder.replicaProvisionedWriteCapacityUnits((dafnyValue.dtor_ReplicaProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaStatus().is_Some()) {
      builder.replicaStatus(ToNative.ReplicaStatus(dafnyValue.dtor_ReplicaStatus().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTableClassSummary().is_Some()) {
      builder.replicaTableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_ReplicaTableClassSummary().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaSettingsDescription> ReplicaSettingsDescriptionList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaSettingsDescription> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaSettingsDescription);
  }

  public static ReplicaSettingsUpdate ReplicaSettingsUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaSettingsUpdate dafnyValue) {
    ReplicaSettingsUpdate.Builder builder = ReplicaSettingsUpdate.builder();
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettingsUpdate().is_Some()) {
      builder.replicaGlobalSecondaryIndexSettingsUpdate(ToNative.ReplicaGlobalSecondaryIndexSettingsUpdateList(dafnyValue.dtor_ReplicaGlobalSecondaryIndexSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate().is_Some()) {
      builder.replicaProvisionedReadCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().is_Some()) {
      builder.replicaProvisionedReadCapacityUnits((dafnyValue.dtor_ReplicaProvisionedReadCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaTableClass().is_Some()) {
      builder.replicaTableClass(ToNative.TableClass(dafnyValue.dtor_ReplicaTableClass().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaSettingsUpdate> ReplicaSettingsUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaSettingsUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaSettingsUpdate);
  }

  public static ReplicaStatus ReplicaStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaStatus dafnyValue) {
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

  public static ReplicationGroupUpdate ReplicationGroupUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicationGroupUpdate dafnyValue) {
    ReplicationGroupUpdate.Builder builder = ReplicationGroupUpdate.builder();
    if (dafnyValue.dtor_Create().is_Some()) {
      builder.create(ToNative.CreateReplicationGroupMemberAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      builder.delete(ToNative.DeleteReplicationGroupMemberAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    if (dafnyValue.dtor_Update().is_Some()) {
      builder.update(ToNative.UpdateReplicationGroupMemberAction(dafnyValue.dtor_Update().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicationGroupUpdate> ReplicationGroupUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicationGroupUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicationGroupUpdate);
  }

  public static ReplicaUpdate ReplicaUpdate(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaUpdate dafnyValue) {
    ReplicaUpdate.Builder builder = ReplicaUpdate.builder();
    if (dafnyValue.dtor_Create().is_Some()) {
      builder.create(ToNative.CreateReplicaAction(dafnyValue.dtor_Create().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      builder.delete(ToNative.DeleteReplicaAction(dafnyValue.dtor_Delete().dtor_value()));
    }
    return builder.build();
  }

  public static List<ReplicaUpdate> ReplicaUpdateList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.ReplicaUpdate> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::ReplicaUpdate);
  }

  public static RestoreSummary RestoreSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.RestoreSummary dafnyValue) {
    RestoreSummary.Builder builder = RestoreSummary.builder();
    builder.restoreDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_RestoreDateTime()));
    builder.restoreInProgress((dafnyValue.dtor_RestoreInProgress()));
    if (dafnyValue.dtor_SourceBackupArn().is_Some()) {
      builder.sourceBackupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceBackupArn().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableArn().is_Some()) {
      builder.sourceTableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableArn().dtor_value()));
    }
    return builder.build();
  }

  public static RestoreTableFromBackupRequest RestoreTableFromBackupInput(
      RestoreTableFromBackupInput dafnyValue) {
    RestoreTableFromBackupRequest.Builder builder = RestoreTableFromBackupRequest.builder();
    builder.backupArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_BackupArn()));
    if (dafnyValue.dtor_BillingModeOverride().is_Some()) {
      builder.billingModeOverride(ToNative.BillingMode(dafnyValue.dtor_BillingModeOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexOverride().is_Some()) {
      builder.globalSecondaryIndexOverride(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexOverride().is_Some()) {
      builder.localSecondaryIndexOverride(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecificationOverride().is_Some()) {
      builder.sseSpecificationOverride(ToNative.SSESpecification(dafnyValue.dtor_SSESpecificationOverride().dtor_value()));
    }
    builder.targetTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetTableName()));
    return builder.build();
  }

  public static RestoreTableFromBackupResponse RestoreTableFromBackupOutput(
      RestoreTableFromBackupOutput dafnyValue) {
    RestoreTableFromBackupResponse.Builder builder = RestoreTableFromBackupResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      builder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static RestoreTableToPointInTimeRequest RestoreTableToPointInTimeInput(
      RestoreTableToPointInTimeInput dafnyValue) {
    RestoreTableToPointInTimeRequest.Builder builder = RestoreTableToPointInTimeRequest.builder();
    if (dafnyValue.dtor_BillingModeOverride().is_Some()) {
      builder.billingModeOverride(ToNative.BillingMode(dafnyValue.dtor_BillingModeOverride().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexOverride().is_Some()) {
      builder.globalSecondaryIndexOverride(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexOverride().is_Some()) {
      builder.localSecondaryIndexOverride(ToNative.LocalSecondaryIndexList(dafnyValue.dtor_LocalSecondaryIndexOverride().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    if (dafnyValue.dtor_RestoreDateTime().is_Some()) {
      builder.restoreDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_RestoreDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableArn().is_Some()) {
      builder.sourceTableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableArn().dtor_value()));
    }
    if (dafnyValue.dtor_SourceTableName().is_Some()) {
      builder.sourceTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_SourceTableName().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecificationOverride().is_Some()) {
      builder.sseSpecificationOverride(ToNative.SSESpecification(dafnyValue.dtor_SSESpecificationOverride().dtor_value()));
    }
    builder.targetTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TargetTableName()));
    if (dafnyValue.dtor_UseLatestRestorableTime().is_Some()) {
      builder.useLatestRestorableTime((dafnyValue.dtor_UseLatestRestorableTime().dtor_value()));
    }
    return builder.build();
  }

  public static RestoreTableToPointInTimeResponse RestoreTableToPointInTimeOutput(
      RestoreTableToPointInTimeOutput dafnyValue) {
    RestoreTableToPointInTimeResponse.Builder builder = RestoreTableToPointInTimeResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      builder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static ReturnConsumedCapacity ReturnConsumedCapacity(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnConsumedCapacity dafnyValue) {
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

  public static ReturnItemCollectionMetrics ReturnItemCollectionMetrics(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnItemCollectionMetrics dafnyValue) {
    if (dafnyValue.is_SIZE()) {
      return ReturnItemCollectionMetrics.SIZE;
    }
    if (dafnyValue.is_NONE()) {
      return ReturnItemCollectionMetrics.NONE;
    }
    return ReturnItemCollectionMetrics.fromValue(dafnyValue.toString());
  }

  public static ReturnValue ReturnValue(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue dafnyValue) {
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

  public static ReturnValuesOnConditionCheckFailure ReturnValuesOnConditionCheckFailure(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValuesOnConditionCheckFailure dafnyValue) {
    if (dafnyValue.is_ALL__OLD()) {
      return ReturnValuesOnConditionCheckFailure.ALL_OLD;
    }
    if (dafnyValue.is_NONE()) {
      return ReturnValuesOnConditionCheckFailure.NONE;
    }
    return ReturnValuesOnConditionCheckFailure.fromValue(dafnyValue.toString());
  }

  public static S3BucketSource S3BucketSource(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.S3BucketSource dafnyValue) {
    S3BucketSource.Builder builder = S3BucketSource.builder();
    builder.s3Bucket(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3Bucket()));
    if (dafnyValue.dtor_S3BucketOwner().is_Some()) {
      builder.s3BucketOwner(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3BucketOwner().dtor_value()));
    }
    if (dafnyValue.dtor_S3KeyPrefix().is_Some()) {
      builder.s3KeyPrefix(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_S3KeyPrefix().dtor_value()));
    }
    return builder.build();
  }

  public static S3SseAlgorithm S3SseAlgorithm(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.S3SseAlgorithm dafnyValue) {
    if (dafnyValue.is_AES256()) {
      return S3SseAlgorithm.AES256;
    }
    if (dafnyValue.is_KMS()) {
      return S3SseAlgorithm.KMS;
    }
    return S3SseAlgorithm.fromValue(dafnyValue.toString());
  }

  public static ScalarAttributeType ScalarAttributeType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.ScalarAttributeType dafnyValue) {
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

  public static ScanRequest ScanInput(ScanInput dafnyValue) {
    ScanRequest.Builder builder = ScanRequest.builder();
    if (dafnyValue.dtor_AttributesToGet().is_Some()) {
      builder.attributesToGet(ToNative.AttributeNameList(dafnyValue.dtor_AttributesToGet().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      builder.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConsistentRead().is_Some()) {
      builder.consistentRead((dafnyValue.dtor_ConsistentRead().dtor_value()));
    }
    if (dafnyValue.dtor_ExclusiveStartKey().is_Some()) {
      builder.exclusiveStartKey(ToNative.Key(dafnyValue.dtor_ExclusiveStartKey().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    if (dafnyValue.dtor_FilterExpression().is_Some()) {
      builder.filterExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_FilterExpression().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_Limit().is_Some()) {
      builder.limit((dafnyValue.dtor_Limit().dtor_value()));
    }
    if (dafnyValue.dtor_ProjectionExpression().is_Some()) {
      builder.projectionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ProjectionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ScanFilter().is_Some()) {
      builder.scanFilter(ToNative.FilterConditionMap(dafnyValue.dtor_ScanFilter().dtor_value()));
    }
    if (dafnyValue.dtor_Segment().is_Some()) {
      builder.segment((dafnyValue.dtor_Segment().dtor_value()));
    }
    if (dafnyValue.dtor_Select().is_Some()) {
      builder.select(ToNative.Select(dafnyValue.dtor_Select().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_TotalSegments().is_Some()) {
      builder.totalSegments((dafnyValue.dtor_TotalSegments().dtor_value()));
    }
    return builder.build();
  }

  public static ScanResponse ScanOutput(ScanOutput dafnyValue) {
    ScanResponse.Builder builder = ScanResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Count().is_Some()) {
      builder.count((dafnyValue.dtor_Count().dtor_value()));
    }
    if (dafnyValue.dtor_Items().is_Some()) {
      builder.items(ToNative.ItemList(dafnyValue.dtor_Items().dtor_value()));
    }
    if (dafnyValue.dtor_LastEvaluatedKey().is_Some()) {
      builder.lastEvaluatedKey(ToNative.Key(dafnyValue.dtor_LastEvaluatedKey().dtor_value()));
    }
    if (dafnyValue.dtor_ScannedCount().is_Some()) {
      builder.scannedCount((dafnyValue.dtor_ScannedCount().dtor_value()));
    }
    return builder.build();
  }

  public static Map<String, Capacity> SecondaryIndexesCapacityMap(
      DafnyMap<? extends DafnySequence<? extends Character>, ? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Capacity> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Capacity);
  }

  public static Select Select(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Select dafnyValue) {
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

  public static SourceTableDetails SourceTableDetails(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SourceTableDetails dafnyValue) {
    SourceTableDetails.Builder builder = SourceTableDetails.builder();
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      builder.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      builder.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput()));
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    builder.tableCreationDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_TableCreationDateTime()));
    builder.tableId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId()));
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_TableSizeBytes().is_Some()) {
      builder.tableSizeBytes((dafnyValue.dtor_TableSizeBytes().dtor_value()));
    }
    return builder.build();
  }

  public static SourceTableFeatureDetails SourceTableFeatureDetails(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SourceTableFeatureDetails dafnyValue) {
    SourceTableFeatureDetails.Builder builder = SourceTableFeatureDetails.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexes(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      builder.localSecondaryIndexes(ToNative.LocalSecondaryIndexes(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_SSEDescription().is_Some()) {
      builder.sseDescription(ToNative.SSEDescription(dafnyValue.dtor_SSEDescription().dtor_value()));
    }
    if (dafnyValue.dtor_StreamDescription().is_Some()) {
      builder.streamDescription(ToNative.StreamSpecification(dafnyValue.dtor_StreamDescription().dtor_value()));
    }
    if (dafnyValue.dtor_TimeToLiveDescription().is_Some()) {
      builder.timeToLiveDescription(ToNative.TimeToLiveDescription(dafnyValue.dtor_TimeToLiveDescription().dtor_value()));
    }
    return builder.build();
  }

  public static SSEDescription SSEDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SSEDescription dafnyValue) {
    SSEDescription.Builder builder = SSEDescription.builder();
    if (dafnyValue.dtor_InaccessibleEncryptionDateTime().is_Some()) {
      builder.inaccessibleEncryptionDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_InaccessibleEncryptionDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyArn().is_Some()) {
      builder.kmsMasterKeyArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyArn().dtor_value()));
    }
    if (dafnyValue.dtor_SSEType().is_Some()) {
      builder.sseType(ToNative.SSEType(dafnyValue.dtor_SSEType().dtor_value()));
    }
    if (dafnyValue.dtor_Status().is_Some()) {
      builder.status(ToNative.SSEStatus(dafnyValue.dtor_Status().dtor_value()));
    }
    return builder.build();
  }

  public static SSESpecification SSESpecification(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SSESpecification dafnyValue) {
    SSESpecification.Builder builder = SSESpecification.builder();
    if (dafnyValue.dtor_Enabled().is_Some()) {
      builder.enabled((dafnyValue.dtor_Enabled().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      builder.kmsMasterKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_SSEType().is_Some()) {
      builder.sseType(ToNative.SSEType(dafnyValue.dtor_SSEType().dtor_value()));
    }
    return builder.build();
  }

  public static SSEStatus SSEStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SSEStatus dafnyValue) {
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

  public static SSEType SSEType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.SSEType dafnyValue) {
    if (dafnyValue.is_AES256()) {
      return SSEType.AES256;
    }
    if (dafnyValue.is_KMS()) {
      return SSEType.KMS;
    }
    return SSEType.fromValue(dafnyValue.toString());
  }

  public static StreamSpecification StreamSpecification(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.StreamSpecification dafnyValue) {
    StreamSpecification.Builder builder = StreamSpecification.builder();
    builder.streamEnabled((dafnyValue.dtor_StreamEnabled()));
    if (dafnyValue.dtor_StreamViewType().is_Some()) {
      builder.streamViewType(ToNative.StreamViewType(dafnyValue.dtor_StreamViewType().dtor_value()));
    }
    return builder.build();
  }

  public static StreamViewType StreamViewType(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.StreamViewType dafnyValue) {
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

  public static List<String> StringSetAttributeValue(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static TableAutoScalingDescription TableAutoScalingDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableAutoScalingDescription dafnyValue) {
    TableAutoScalingDescription.Builder builder = TableAutoScalingDescription.builder();
    if (dafnyValue.dtor_Replicas().is_Some()) {
      builder.replicas(ToNative.ReplicaAutoScalingDescriptionList(dafnyValue.dtor_Replicas().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_TableStatus().is_Some()) {
      builder.tableStatus(ToNative.TableStatus(dafnyValue.dtor_TableStatus().dtor_value()));
    }
    return builder.build();
  }

  public static TableClass TableClass(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableClass dafnyValue) {
    if (dafnyValue.is_STANDARD()) {
      return TableClass.STANDARD;
    }
    if (dafnyValue.is_STANDARD__INFREQUENT__ACCESS()) {
      return TableClass.STANDARD_INFREQUENT_ACCESS;
    }
    return TableClass.fromValue(dafnyValue.toString());
  }

  public static TableClassSummary TableClassSummary(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableClassSummary dafnyValue) {
    TableClassSummary.Builder builder = TableClassSummary.builder();
    if (dafnyValue.dtor_LastUpdateDateTime().is_Some()) {
      builder.lastUpdateDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_LastUpdateDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_TableClass().is_Some()) {
      builder.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    return builder.build();
  }

  public static TableCreationParameters TableCreationParameters(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableCreationParameters dafnyValue) {
    TableCreationParameters.Builder builder = TableCreationParameters.builder();
    builder.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions()));
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      builder.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema()));
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      builder.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static TableDescription TableDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableDescription dafnyValue) {
    TableDescription.Builder builder = TableDescription.builder();
    if (dafnyValue.dtor_ArchivalSummary().is_Some()) {
      builder.archivalSummary(ToNative.ArchivalSummary(dafnyValue.dtor_ArchivalSummary().dtor_value()));
    }
    if (dafnyValue.dtor_AttributeDefinitions().is_Some()) {
      builder.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions().dtor_value()));
    }
    if (dafnyValue.dtor_BillingModeSummary().is_Some()) {
      builder.billingModeSummary(ToNative.BillingModeSummary(dafnyValue.dtor_BillingModeSummary().dtor_value()));
    }
    if (dafnyValue.dtor_CreationDateTime().is_Some()) {
      builder.creationDateTime(software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(dafnyValue.dtor_CreationDateTime().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.GlobalSecondaryIndexDescriptionList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableVersion().is_Some()) {
      builder.globalTableVersion(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableVersion().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCount().is_Some()) {
      builder.itemCount((dafnyValue.dtor_ItemCount().dtor_value()));
    }
    if (dafnyValue.dtor_KeySchema().is_Some()) {
      builder.keySchema(ToNative.KeySchema(dafnyValue.dtor_KeySchema().dtor_value()));
    }
    if (dafnyValue.dtor_LatestStreamArn().is_Some()) {
      builder.latestStreamArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LatestStreamArn().dtor_value()));
    }
    if (dafnyValue.dtor_LatestStreamLabel().is_Some()) {
      builder.latestStreamLabel(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_LatestStreamLabel().dtor_value()));
    }
    if (dafnyValue.dtor_LocalSecondaryIndexes().is_Some()) {
      builder.localSecondaryIndexes(ToNative.LocalSecondaryIndexDescriptionList(dafnyValue.dtor_LocalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughputDescription(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_Replicas().is_Some()) {
      builder.replicas(ToNative.ReplicaDescriptionList(dafnyValue.dtor_Replicas().dtor_value()));
    }
    if (dafnyValue.dtor_RestoreSummary().is_Some()) {
      builder.restoreSummary(ToNative.RestoreSummary(dafnyValue.dtor_RestoreSummary().dtor_value()));
    }
    if (dafnyValue.dtor_SSEDescription().is_Some()) {
      builder.sseDescription(ToNative.SSEDescription(dafnyValue.dtor_SSEDescription().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      builder.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_TableArn().is_Some()) {
      builder.tableArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableArn().dtor_value()));
    }
    if (dafnyValue.dtor_TableClassSummary().is_Some()) {
      builder.tableClassSummary(ToNative.TableClassSummary(dafnyValue.dtor_TableClassSummary().dtor_value()));
    }
    if (dafnyValue.dtor_TableId().is_Some()) {
      builder.tableId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableId().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    if (dafnyValue.dtor_TableSizeBytes().is_Some()) {
      builder.tableSizeBytes((dafnyValue.dtor_TableSizeBytes().dtor_value()));
    }
    if (dafnyValue.dtor_TableStatus().is_Some()) {
      builder.tableStatus(ToNative.TableStatus(dafnyValue.dtor_TableStatus().dtor_value()));
    }
    return builder.build();
  }

  public static List<String> TableNameList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static TableStatus TableStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TableStatus dafnyValue) {
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

  public static Tag Tag(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Tag dafnyValue) {
    Tag.Builder builder = Tag.builder();
    builder.key(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Key()));
    builder.value(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Value()));
    return builder.build();
  }

  public static List<String> TagKeyList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
  }

  public static List<Tag> TagList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.Tag> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::Tag);
  }

  public static TagResourceRequest TagResourceInput(TagResourceInput dafnyValue) {
    TagResourceRequest.Builder builder = TagResourceRequest.builder();
    builder.resourceArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    builder.tags(ToNative.TagList(dafnyValue.dtor_Tags()));
    return builder.build();
  }

  public static TimeToLiveDescription TimeToLiveDescription(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TimeToLiveDescription dafnyValue) {
    TimeToLiveDescription.Builder builder = TimeToLiveDescription.builder();
    if (dafnyValue.dtor_AttributeName().is_Some()) {
      builder.attributeName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName().dtor_value()));
    }
    if (dafnyValue.dtor_TimeToLiveStatus().is_Some()) {
      builder.timeToLiveStatus(ToNative.TimeToLiveStatus(dafnyValue.dtor_TimeToLiveStatus().dtor_value()));
    }
    return builder.build();
  }

  public static TimeToLiveSpecification TimeToLiveSpecification(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TimeToLiveSpecification dafnyValue) {
    TimeToLiveSpecification.Builder builder = TimeToLiveSpecification.builder();
    builder.attributeName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_AttributeName()));
    builder.enabled((dafnyValue.dtor_Enabled()));
    return builder.build();
  }

  public static TimeToLiveStatus TimeToLiveStatus(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TimeToLiveStatus dafnyValue) {
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

  public static TransactGetItem TransactGetItem(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactGetItem dafnyValue) {
    TransactGetItem.Builder builder = TransactGetItem.builder();
    builder.get(ToNative.Get(dafnyValue.dtor_Get()));
    return builder.build();
  }

  public static List<TransactGetItem> TransactGetItemList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactGetItem> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::TransactGetItem);
  }

  public static TransactGetItemsRequest TransactGetItemsInput(TransactGetItemsInput dafnyValue) {
    TransactGetItemsRequest.Builder builder = TransactGetItemsRequest.builder();
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    builder.transactItems(ToNative.TransactGetItemList(dafnyValue.dtor_TransactItems()));
    return builder.build();
  }

  public static TransactGetItemsResponse TransactGetItemsOutput(TransactGetItemsOutput dafnyValue) {
    TransactGetItemsResponse.Builder builder = TransactGetItemsResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_Responses().is_Some()) {
      builder.responses(ToNative.ItemResponseList(dafnyValue.dtor_Responses().dtor_value()));
    }
    return builder.build();
  }

  public static TransactWriteItem TransactWriteItem(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactWriteItem dafnyValue) {
    TransactWriteItem.Builder builder = TransactWriteItem.builder();
    if (dafnyValue.dtor_ConditionCheck().is_Some()) {
      builder.conditionCheck(ToNative.ConditionCheck(dafnyValue.dtor_ConditionCheck().dtor_value()));
    }
    if (dafnyValue.dtor_Delete().is_Some()) {
      builder.delete(ToNative.Delete(dafnyValue.dtor_Delete().dtor_value()));
    }
    if (dafnyValue.dtor_Put().is_Some()) {
      builder.put(ToNative.Put(dafnyValue.dtor_Put().dtor_value()));
    }
    if (dafnyValue.dtor_Update().is_Some()) {
      builder.update(ToNative.Update(dafnyValue.dtor_Update().dtor_value()));
    }
    return builder.build();
  }

  public static List<TransactWriteItem> TransactWriteItemList(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.TransactWriteItem> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::TransactWriteItem);
  }

  public static TransactWriteItemsRequest TransactWriteItemsInput(
      TransactWriteItemsInput dafnyValue) {
    TransactWriteItemsRequest.Builder builder = TransactWriteItemsRequest.builder();
    if (dafnyValue.dtor_ClientRequestToken().is_Some()) {
      builder.clientRequestToken(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ClientRequestToken().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      builder.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    builder.transactItems(ToNative.TransactWriteItemList(dafnyValue.dtor_TransactItems()));
    return builder.build();
  }

  public static TransactWriteItemsResponse TransactWriteItemsOutput(
      TransactWriteItemsOutput dafnyValue) {
    TransactWriteItemsResponse.Builder builder = TransactWriteItemsResponse.builder();
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacityMultiple(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      builder.itemCollectionMetrics(ToNative.ItemCollectionMetricsPerTable(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return builder.build();
  }

  public static UntagResourceRequest UntagResourceInput(UntagResourceInput dafnyValue) {
    UntagResourceRequest.Builder builder = UntagResourceRequest.builder();
    builder.resourceArn(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ResourceArn()));
    builder.tagKeys(ToNative.TagKeyList(dafnyValue.dtor_TagKeys()));
    return builder.build();
  }

  public static Update Update(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.Update dafnyValue) {
    Update.Builder builder = Update.builder();
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().is_Some()) {
      builder.returnValuesOnConditionCheckFailure(ToNative.ReturnValuesOnConditionCheckFailure(dafnyValue.dtor_ReturnValuesOnConditionCheckFailure().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    builder.updateExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_UpdateExpression()));
    return builder.build();
  }

  public static UpdateContinuousBackupsRequest UpdateContinuousBackupsInput(
      UpdateContinuousBackupsInput dafnyValue) {
    UpdateContinuousBackupsRequest.Builder builder = UpdateContinuousBackupsRequest.builder();
    builder.pointInTimeRecoverySpecification(ToNative.PointInTimeRecoverySpecification(dafnyValue.dtor_PointInTimeRecoverySpecification()));
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static UpdateContinuousBackupsResponse UpdateContinuousBackupsOutput(
      UpdateContinuousBackupsOutput dafnyValue) {
    UpdateContinuousBackupsResponse.Builder builder = UpdateContinuousBackupsResponse.builder();
    if (dafnyValue.dtor_ContinuousBackupsDescription().is_Some()) {
      builder.continuousBackupsDescription(ToNative.ContinuousBackupsDescription(dafnyValue.dtor_ContinuousBackupsDescription().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateContributorInsightsRequest UpdateContributorInsightsInput(
      UpdateContributorInsightsInput dafnyValue) {
    UpdateContributorInsightsRequest.Builder builder = UpdateContributorInsightsRequest.builder();
    builder.contributorInsightsAction(ToNative.ContributorInsightsAction(dafnyValue.dtor_ContributorInsightsAction()));
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static UpdateContributorInsightsResponse UpdateContributorInsightsOutput(
      UpdateContributorInsightsOutput dafnyValue) {
    UpdateContributorInsightsResponse.Builder builder = UpdateContributorInsightsResponse.builder();
    if (dafnyValue.dtor_ContributorInsightsStatus().is_Some()) {
      builder.contributorInsightsStatus(ToNative.ContributorInsightsStatus(dafnyValue.dtor_ContributorInsightsStatus().dtor_value()));
    }
    if (dafnyValue.dtor_IndexName().is_Some()) {
      builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName().dtor_value()));
    }
    if (dafnyValue.dtor_TableName().is_Some()) {
      builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateGlobalSecondaryIndexAction UpdateGlobalSecondaryIndexAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateGlobalSecondaryIndexAction dafnyValue) {
    UpdateGlobalSecondaryIndexAction.Builder builder = UpdateGlobalSecondaryIndexAction.builder();
    builder.indexName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_IndexName()));
    builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput()));
    return builder.build();
  }

  public static UpdateGlobalTableRequest UpdateGlobalTableInput(UpdateGlobalTableInput dafnyValue) {
    UpdateGlobalTableRequest.Builder builder = UpdateGlobalTableRequest.builder();
    builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    builder.replicaUpdates(ToNative.ReplicaUpdateList(dafnyValue.dtor_ReplicaUpdates()));
    return builder.build();
  }

  public static UpdateGlobalTableResponse UpdateGlobalTableOutput(
      UpdateGlobalTableOutput dafnyValue) {
    UpdateGlobalTableResponse.Builder builder = UpdateGlobalTableResponse.builder();
    if (dafnyValue.dtor_GlobalTableDescription().is_Some()) {
      builder.globalTableDescription(ToNative.GlobalTableDescription(dafnyValue.dtor_GlobalTableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateGlobalTableSettingsRequest UpdateGlobalTableSettingsInput(
      UpdateGlobalTableSettingsInput dafnyValue) {
    UpdateGlobalTableSettingsRequest.Builder builder = UpdateGlobalTableSettingsRequest.builder();
    if (dafnyValue.dtor_GlobalTableBillingMode().is_Some()) {
      builder.globalTableBillingMode(ToNative.BillingMode(dafnyValue.dtor_GlobalTableBillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableGlobalSecondaryIndexSettingsUpdate().is_Some()) {
      builder.globalTableGlobalSecondaryIndexSettingsUpdate(ToNative.GlobalTableGlobalSecondaryIndexSettingsUpdateList(dafnyValue.dtor_GlobalTableGlobalSecondaryIndexSettingsUpdate().dtor_value()));
    }
    builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName()));
    if (dafnyValue.dtor_GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate().is_Some()) {
      builder.globalTableProvisionedWriteCapacityAutoScalingSettingsUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalTableProvisionedWriteCapacityUnits().is_Some()) {
      builder.globalTableProvisionedWriteCapacityUnits((dafnyValue.dtor_GlobalTableProvisionedWriteCapacityUnits().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettingsUpdate().is_Some()) {
      builder.replicaSettingsUpdate(ToNative.ReplicaSettingsUpdateList(dafnyValue.dtor_ReplicaSettingsUpdate().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateGlobalTableSettingsResponse UpdateGlobalTableSettingsOutput(
      UpdateGlobalTableSettingsOutput dafnyValue) {
    UpdateGlobalTableSettingsResponse.Builder builder = UpdateGlobalTableSettingsResponse.builder();
    if (dafnyValue.dtor_GlobalTableName().is_Some()) {
      builder.globalTableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_GlobalTableName().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaSettings().is_Some()) {
      builder.replicaSettings(ToNative.ReplicaSettingsDescriptionList(dafnyValue.dtor_ReplicaSettings().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateItemRequest UpdateItemInput(UpdateItemInput dafnyValue) {
    UpdateItemRequest.Builder builder = UpdateItemRequest.builder();
    if (dafnyValue.dtor_AttributeUpdates().is_Some()) {
      builder.attributeUpdates(ToNative.AttributeUpdates(dafnyValue.dtor_AttributeUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionalOperator().is_Some()) {
      builder.conditionalOperator(ToNative.ConditionalOperator(dafnyValue.dtor_ConditionalOperator().dtor_value()));
    }
    if (dafnyValue.dtor_ConditionExpression().is_Some()) {
      builder.conditionExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ConditionExpression().dtor_value()));
    }
    if (dafnyValue.dtor_Expected().is_Some()) {
      builder.expected(ToNative.ExpectedAttributeMap(dafnyValue.dtor_Expected().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeNames().is_Some()) {
      builder.expressionAttributeNames(ToNative.ExpressionAttributeNameMap(dafnyValue.dtor_ExpressionAttributeNames().dtor_value()));
    }
    if (dafnyValue.dtor_ExpressionAttributeValues().is_Some()) {
      builder.expressionAttributeValues(ToNative.ExpressionAttributeValueMap(dafnyValue.dtor_ExpressionAttributeValues().dtor_value()));
    }
    builder.key(ToNative.Key(dafnyValue.dtor_Key()));
    if (dafnyValue.dtor_ReturnConsumedCapacity().is_Some()) {
      builder.returnConsumedCapacity(ToNative.ReturnConsumedCapacity(dafnyValue.dtor_ReturnConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnItemCollectionMetrics().is_Some()) {
      builder.returnItemCollectionMetrics(ToNative.ReturnItemCollectionMetrics(dafnyValue.dtor_ReturnItemCollectionMetrics().dtor_value()));
    }
    if (dafnyValue.dtor_ReturnValues().is_Some()) {
      builder.returnValues(ToNative.ReturnValue(dafnyValue.dtor_ReturnValues().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    if (dafnyValue.dtor_UpdateExpression().is_Some()) {
      builder.updateExpression(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_UpdateExpression().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateItemResponse UpdateItemOutput(UpdateItemOutput dafnyValue) {
    UpdateItemResponse.Builder builder = UpdateItemResponse.builder();
    if (dafnyValue.dtor_Attributes().is_Some()) {
      builder.attributes(ToNative.AttributeMap(dafnyValue.dtor_Attributes().dtor_value()));
    }
    if (dafnyValue.dtor_ConsumedCapacity().is_Some()) {
      builder.consumedCapacity(ToNative.ConsumedCapacity(dafnyValue.dtor_ConsumedCapacity().dtor_value()));
    }
    if (dafnyValue.dtor_ItemCollectionMetrics().is_Some()) {
      builder.itemCollectionMetrics(ToNative.ItemCollectionMetrics(dafnyValue.dtor_ItemCollectionMetrics().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateReplicationGroupMemberAction UpdateReplicationGroupMemberAction(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateReplicationGroupMemberAction dafnyValue) {
    UpdateReplicationGroupMemberAction.Builder builder = UpdateReplicationGroupMemberAction.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexes().is_Some()) {
      builder.globalSecondaryIndexes(ToNative.ReplicaGlobalSecondaryIndexList(dafnyValue.dtor_GlobalSecondaryIndexes().dtor_value()));
    }
    if (dafnyValue.dtor_KMSMasterKeyId().is_Some()) {
      builder.kmsMasterKeyId(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_KMSMasterKeyId().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughputOverride().is_Some()) {
      builder.provisionedThroughputOverride(ToNative.ProvisionedThroughputOverride(dafnyValue.dtor_ProvisionedThroughputOverride().dtor_value()));
    }
    builder.regionName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_RegionName()));
    if (dafnyValue.dtor_TableClassOverride().is_Some()) {
      builder.tableClassOverride(ToNative.TableClass(dafnyValue.dtor_TableClassOverride().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateTableRequest UpdateTableInput(UpdateTableInput dafnyValue) {
    UpdateTableRequest.Builder builder = UpdateTableRequest.builder();
    if (dafnyValue.dtor_AttributeDefinitions().is_Some()) {
      builder.attributeDefinitions(ToNative.AttributeDefinitions(dafnyValue.dtor_AttributeDefinitions().dtor_value()));
    }
    if (dafnyValue.dtor_BillingMode().is_Some()) {
      builder.billingMode(ToNative.BillingMode(dafnyValue.dtor_BillingMode().dtor_value()));
    }
    if (dafnyValue.dtor_GlobalSecondaryIndexUpdates().is_Some()) {
      builder.globalSecondaryIndexUpdates(ToNative.GlobalSecondaryIndexUpdateList(dafnyValue.dtor_GlobalSecondaryIndexUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedThroughput().is_Some()) {
      builder.provisionedThroughput(ToNative.ProvisionedThroughput(dafnyValue.dtor_ProvisionedThroughput().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaUpdates().is_Some()) {
      builder.replicaUpdates(ToNative.ReplicationGroupUpdateList(dafnyValue.dtor_ReplicaUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_SSESpecification().is_Some()) {
      builder.sseSpecification(ToNative.SSESpecification(dafnyValue.dtor_SSESpecification().dtor_value()));
    }
    if (dafnyValue.dtor_StreamSpecification().is_Some()) {
      builder.streamSpecification(ToNative.StreamSpecification(dafnyValue.dtor_StreamSpecification().dtor_value()));
    }
    if (dafnyValue.dtor_TableClass().is_Some()) {
      builder.tableClass(ToNative.TableClass(dafnyValue.dtor_TableClass().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static UpdateTableResponse UpdateTableOutput(UpdateTableOutput dafnyValue) {
    UpdateTableResponse.Builder builder = UpdateTableResponse.builder();
    if (dafnyValue.dtor_TableDescription().is_Some()) {
      builder.tableDescription(ToNative.TableDescription(dafnyValue.dtor_TableDescription().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateTableReplicaAutoScalingRequest UpdateTableReplicaAutoScalingInput(
      UpdateTableReplicaAutoScalingInput dafnyValue) {
    UpdateTableReplicaAutoScalingRequest.Builder builder = UpdateTableReplicaAutoScalingRequest.builder();
    if (dafnyValue.dtor_GlobalSecondaryIndexUpdates().is_Some()) {
      builder.globalSecondaryIndexUpdates(ToNative.GlobalSecondaryIndexAutoScalingUpdateList(dafnyValue.dtor_GlobalSecondaryIndexUpdates().dtor_value()));
    }
    if (dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().is_Some()) {
      builder.provisionedWriteCapacityAutoScalingUpdate(ToNative.AutoScalingSettingsUpdate(dafnyValue.dtor_ProvisionedWriteCapacityAutoScalingUpdate().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicaUpdates().is_Some()) {
      builder.replicaUpdates(ToNative.ReplicaAutoScalingUpdateList(dafnyValue.dtor_ReplicaUpdates().dtor_value()));
    }
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    return builder.build();
  }

  public static UpdateTableReplicaAutoScalingResponse UpdateTableReplicaAutoScalingOutput(
      UpdateTableReplicaAutoScalingOutput dafnyValue) {
    UpdateTableReplicaAutoScalingResponse.Builder builder = UpdateTableReplicaAutoScalingResponse.builder();
    if (dafnyValue.dtor_TableAutoScalingDescription().is_Some()) {
      builder.tableAutoScalingDescription(ToNative.TableAutoScalingDescription(dafnyValue.dtor_TableAutoScalingDescription().dtor_value()));
    }
    return builder.build();
  }

  public static UpdateTimeToLiveRequest UpdateTimeToLiveInput(UpdateTimeToLiveInput dafnyValue) {
    UpdateTimeToLiveRequest.Builder builder = UpdateTimeToLiveRequest.builder();
    builder.tableName(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_TableName()));
    builder.timeToLiveSpecification(ToNative.TimeToLiveSpecification(dafnyValue.dtor_TimeToLiveSpecification()));
    return builder.build();
  }

  public static UpdateTimeToLiveResponse UpdateTimeToLiveOutput(UpdateTimeToLiveOutput dafnyValue) {
    UpdateTimeToLiveResponse.Builder builder = UpdateTimeToLiveResponse.builder();
    if (dafnyValue.dtor_TimeToLiveSpecification().is_Some()) {
      builder.timeToLiveSpecification(ToNative.TimeToLiveSpecification(dafnyValue.dtor_TimeToLiveSpecification().dtor_value()));
    }
    return builder.build();
  }

  public static WriteRequest WriteRequest(
      software.amazon.cryptography.services.dynamodb.internaldafny.types.WriteRequest dafnyValue) {
    WriteRequest.Builder builder = WriteRequest.builder();
    if (dafnyValue.dtor_DeleteRequest().is_Some()) {
      builder.deleteRequest(ToNative.DeleteRequest(dafnyValue.dtor_DeleteRequest().dtor_value()));
    }
    if (dafnyValue.dtor_PutRequest().is_Some()) {
      builder.putRequest(ToNative.PutRequest(dafnyValue.dtor_PutRequest().dtor_value()));
    }
    return builder.build();
  }

  public static List<WriteRequest> WriteRequests(
      DafnySequence<? extends software.amazon.cryptography.services.dynamodb.internaldafny.types.WriteRequest> dafnyValue) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.cryptography.services.dynamodb.internaldafny.ToNative::WriteRequest);
  }

  public static BackupInUseException Error(Error_BackupInUseException dafnyValue) {
    BackupInUseException.Builder builder = BackupInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static BackupNotFoundException Error(Error_BackupNotFoundException dafnyValue) {
    BackupNotFoundException.Builder builder = BackupNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ConditionalCheckFailedException Error(
      Error_ConditionalCheckFailedException dafnyValue) {
    ConditionalCheckFailedException.Builder builder = ConditionalCheckFailedException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ContinuousBackupsUnavailableException Error(
      Error_ContinuousBackupsUnavailableException dafnyValue) {
    ContinuousBackupsUnavailableException.Builder builder = ContinuousBackupsUnavailableException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static DuplicateItemException Error(Error_DuplicateItemException dafnyValue) {
    DuplicateItemException.Builder builder = DuplicateItemException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ExportConflictException Error(Error_ExportConflictException dafnyValue) {
    ExportConflictException.Builder builder = ExportConflictException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ExportNotFoundException Error(Error_ExportNotFoundException dafnyValue) {
    ExportNotFoundException.Builder builder = ExportNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalTableAlreadyExistsException Error(
      Error_GlobalTableAlreadyExistsException dafnyValue) {
    GlobalTableAlreadyExistsException.Builder builder = GlobalTableAlreadyExistsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static GlobalTableNotFoundException Error(Error_GlobalTableNotFoundException dafnyValue) {
    GlobalTableNotFoundException.Builder builder = GlobalTableNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IdempotentParameterMismatchException Error(
      Error_IdempotentParameterMismatchException dafnyValue) {
    IdempotentParameterMismatchException.Builder builder = IdempotentParameterMismatchException.builder();
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return builder.build();
  }

  public static ImportConflictException Error(Error_ImportConflictException dafnyValue) {
    ImportConflictException.Builder builder = ImportConflictException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ImportNotFoundException Error(Error_ImportNotFoundException dafnyValue) {
    ImportNotFoundException.Builder builder = ImportNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static IndexNotFoundException Error(Error_IndexNotFoundException dafnyValue) {
    IndexNotFoundException.Builder builder = IndexNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InternalServerErrorException Error(Error_InternalServerError dafnyValue) {
    InternalServerErrorException.Builder builder = InternalServerErrorException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidExportTimeException Error(Error_InvalidExportTimeException dafnyValue) {
    InvalidExportTimeException.Builder builder = InvalidExportTimeException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static InvalidRestoreTimeException Error(Error_InvalidRestoreTimeException dafnyValue) {
    InvalidRestoreTimeException.Builder builder = InvalidRestoreTimeException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ItemCollectionSizeLimitExceededException Error(
      Error_ItemCollectionSizeLimitExceededException dafnyValue) {
    ItemCollectionSizeLimitExceededException.Builder builder = ItemCollectionSizeLimitExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static LimitExceededException Error(Error_LimitExceededException dafnyValue) {
    LimitExceededException.Builder builder = LimitExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static PointInTimeRecoveryUnavailableException Error(
      Error_PointInTimeRecoveryUnavailableException dafnyValue) {
    PointInTimeRecoveryUnavailableException.Builder builder = PointInTimeRecoveryUnavailableException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ProvisionedThroughputExceededException Error(
      Error_ProvisionedThroughputExceededException dafnyValue) {
    ProvisionedThroughputExceededException.Builder builder = ProvisionedThroughputExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicaAlreadyExistsException Error(
      Error_ReplicaAlreadyExistsException dafnyValue) {
    ReplicaAlreadyExistsException.Builder builder = ReplicaAlreadyExistsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ReplicaNotFoundException Error(Error_ReplicaNotFoundException dafnyValue) {
    ReplicaNotFoundException.Builder builder = ReplicaNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static RequestLimitExceededException Error(Error_RequestLimitExceeded dafnyValue) {
    RequestLimitExceededException.Builder builder = RequestLimitExceededException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ResourceInUseException Error(Error_ResourceInUseException dafnyValue) {
    ResourceInUseException.Builder builder = ResourceInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static ResourceNotFoundException Error(Error_ResourceNotFoundException dafnyValue) {
    ResourceNotFoundException.Builder builder = ResourceNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TableAlreadyExistsException Error(Error_TableAlreadyExistsException dafnyValue) {
    TableAlreadyExistsException.Builder builder = TableAlreadyExistsException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TableInUseException Error(Error_TableInUseException dafnyValue) {
    TableInUseException.Builder builder = TableInUseException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TableNotFoundException Error(Error_TableNotFoundException dafnyValue) {
    TableNotFoundException.Builder builder = TableNotFoundException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TransactionCanceledException Error(Error_TransactionCanceledException dafnyValue) {
    TransactionCanceledException.Builder builder = TransactionCanceledException.builder();
    if (dafnyValue.dtor_CancellationReasons().is_Some()) {
      builder.cancellationReasons(ToNative.CancellationReasonList(dafnyValue.dtor_CancellationReasons().dtor_value()));
    }
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return builder.build();
  }

  public static TransactionConflictException Error(Error_TransactionConflictException dafnyValue) {
    TransactionConflictException.Builder builder = TransactionConflictException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
    }
    return builder.build();
  }

  public static TransactionInProgressException Error(
      Error_TransactionInProgressException dafnyValue) {
    TransactionInProgressException.Builder builder = TransactionInProgressException.builder();
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_Message().dtor_value()));
    }
    return builder.build();
  }

  // BEGIN MANUAL EDIT
  public static RuntimeException Error(software.amazon.cryptography.services.dynamodb.internaldafny.types.Error dafnyValue) {
    if (dafnyValue.is_BackupInUseException()) {
      return ToNative.Error((Error_BackupInUseException) dafnyValue);
    }
    if (dafnyValue.is_BackupNotFoundException()) {
      return ToNative.Error((Error_BackupNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_ConditionalCheckFailedException()) {
      return ToNative.Error((Error_ConditionalCheckFailedException) dafnyValue);
    }
    if (dafnyValue.is_ContinuousBackupsUnavailableException()) {
      return ToNative.Error((Error_ContinuousBackupsUnavailableException) dafnyValue);
    }
    if (dafnyValue.is_DuplicateItemException()) {
      return ToNative.Error((Error_DuplicateItemException) dafnyValue);
    }
    if (dafnyValue.is_ExportConflictException()) {
      return ToNative.Error((Error_ExportConflictException) dafnyValue);
    }
    if (dafnyValue.is_ExportNotFoundException()) {
      return ToNative.Error((Error_ExportNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_GlobalTableAlreadyExistsException()) {
      return ToNative.Error((Error_GlobalTableAlreadyExistsException) dafnyValue);
    }
    if (dafnyValue.is_GlobalTableNotFoundException()) {
      return ToNative.Error((Error_GlobalTableNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_IdempotentParameterMismatchException()) {
      return ToNative.Error((Error_IdempotentParameterMismatchException) dafnyValue);
    }
    if (dafnyValue.is_ImportConflictException()) {
      return ToNative.Error((Error_ImportConflictException) dafnyValue);
    }
    if (dafnyValue.is_ImportNotFoundException()) {
      return ToNative.Error((Error_ImportNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_IndexNotFoundException()) {
      return ToNative.Error((Error_IndexNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_InternalServerError()) {
      return ToNative.Error((Error_InternalServerError) dafnyValue);
    }
    if (dafnyValue.is_InvalidExportTimeException()) {
      return ToNative.Error((Error_InvalidExportTimeException) dafnyValue);
    }
    if (dafnyValue.is_InvalidRestoreTimeException()) {
      return ToNative.Error((Error_InvalidRestoreTimeException) dafnyValue);
    }
    if (dafnyValue.is_ItemCollectionSizeLimitExceededException()) {
      return ToNative.Error((Error_ItemCollectionSizeLimitExceededException) dafnyValue);
    }
    if (dafnyValue.is_LimitExceededException()) {
      return ToNative.Error((Error_LimitExceededException) dafnyValue);
    }
    if (dafnyValue.is_PointInTimeRecoveryUnavailableException()) {
      return ToNative.Error((Error_PointInTimeRecoveryUnavailableException) dafnyValue);
    }
    if (dafnyValue.is_ProvisionedThroughputExceededException()) {
      return ToNative.Error((Error_ProvisionedThroughputExceededException) dafnyValue);
    }
    if (dafnyValue.is_ReplicaAlreadyExistsException()) {
      return ToNative.Error((Error_ReplicaAlreadyExistsException) dafnyValue);
    }
    if (dafnyValue.is_ReplicaNotFoundException()) {
      return ToNative.Error((Error_ReplicaNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_RequestLimitExceeded()) {
      return ToNative.Error((Error_RequestLimitExceeded) dafnyValue);
    }
    if (dafnyValue.is_ResourceInUseException()) {
      return ToNative.Error((Error_ResourceInUseException) dafnyValue);
    }
    if (dafnyValue.is_ResourceNotFoundException()) {
      return ToNative.Error((Error_ResourceNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_TableAlreadyExistsException()) {
      return ToNative.Error((Error_TableAlreadyExistsException) dafnyValue);
    }
    if (dafnyValue.is_TableInUseException()) {
      return ToNative.Error((Error_TableInUseException) dafnyValue);
    }
    if (dafnyValue.is_TableNotFoundException()) {
      return ToNative.Error((Error_TableNotFoundException) dafnyValue);
    }
    if (dafnyValue.is_TransactionCanceledException()) {
      return ToNative.Error((Error_TransactionCanceledException) dafnyValue);
    }
    if (dafnyValue.is_TransactionConflictException()) {
      return ToNative.Error((Error_TransactionConflictException) dafnyValue);
    }
    if (dafnyValue.is_TransactionInProgressException()) {
      return ToNative.Error((Error_TransactionInProgressException) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    // TODO This should indicate a codegen bug
    return new IllegalStateException("Unknown error recieved from DynamoDb.");
  }
// END MANUAL EDIT

  public static DynamoDbClient DynamoDB_20120810(IDynamoDBClient dafnyValue) {
    return ((Shim) dafnyValue).impl();
  }
}
