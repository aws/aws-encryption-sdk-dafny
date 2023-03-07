// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/src/Index.dfy"
 module {:extern "Dafny.Com.Amazonaws.Dynamodb.Types" } ComAmazonawsDynamodbTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 type ArchivalReason = string
 datatype ArchivalSummary = | ArchivalSummary (
 nameonly ArchivalDateTime: Option<string> ,
 nameonly ArchivalReason: Option<ArchivalReason> ,
 nameonly ArchivalBackupArn: Option<BackupArn>
 )
 datatype AttributeAction =
	| ADD
	| PUT
	| DELETE
 datatype AttributeDefinition = | AttributeDefinition (
 nameonly AttributeName: KeySchemaAttributeName ,
 nameonly AttributeType: ScalarAttributeType
 )
 type AttributeDefinitions = seq<AttributeDefinition>
 type AttributeMap = map<AttributeName, AttributeValue>
 type AttributeName = x: string | IsValid_AttributeName(x) witness *
 predicate method IsValid_AttributeName(x: string) {
 ( 0 <= |x| <= 65535 )
}
 type AttributeNameList = x: seq<AttributeName> | IsValid_AttributeNameList(x) witness *
 predicate method IsValid_AttributeNameList(x: seq<AttributeName>) {
 ( 1 <= |x|  )
}
 type AttributeUpdates = map<AttributeName, AttributeValueUpdate>
 datatype AttributeValue =
 | S(S: StringAttributeValue)
 | N(N: NumberAttributeValue)
 | B(B: BinaryAttributeValue)
 | SS(SS: StringSetAttributeValue)
 | NS(NS: NumberSetAttributeValue)
 | BS(BS: BinarySetAttributeValue)
 | M(M: MapAttributeValue)
 | L(L: ListAttributeValue)
 | NULL(NULL: NullAttributeValue)
 | BOOL(BOOL: BooleanAttributeValue)
 type AttributeValueList = seq<AttributeValue>
 datatype AttributeValueUpdate = | AttributeValueUpdate (
 nameonly Value: Option<AttributeValue> ,
 nameonly Action: Option<AttributeAction>
 )
 datatype AutoScalingPolicyDescription = | AutoScalingPolicyDescription (
 nameonly PolicyName: Option<AutoScalingPolicyName> ,
 nameonly TargetTrackingScalingPolicyConfiguration: Option<AutoScalingTargetTrackingScalingPolicyConfigurationDescription>
 )
 type AutoScalingPolicyDescriptionList = seq<AutoScalingPolicyDescription>
 type AutoScalingPolicyName = x: string | IsValid_AutoScalingPolicyName(x) witness *
 predicate method IsValid_AutoScalingPolicyName(x: string) {
 ( 1 <= |x| <= 256 )
}
 datatype AutoScalingPolicyUpdate = | AutoScalingPolicyUpdate (
 nameonly PolicyName: Option<AutoScalingPolicyName> ,
 nameonly TargetTrackingScalingPolicyConfiguration: AutoScalingTargetTrackingScalingPolicyConfigurationUpdate
 )
 type AutoScalingRoleArn = x: string | IsValid_AutoScalingRoleArn(x) witness *
 predicate method IsValid_AutoScalingRoleArn(x: string) {
 ( 1 <= |x| <= 1600 )
}
 datatype AutoScalingSettingsDescription = | AutoScalingSettingsDescription (
 nameonly MinimumUnits: Option<PositiveLongObject> ,
 nameonly MaximumUnits: Option<PositiveLongObject> ,
 nameonly AutoScalingDisabled: Option<BooleanObject> ,
 nameonly AutoScalingRoleArn: Option<String> ,
 nameonly ScalingPolicies: Option<AutoScalingPolicyDescriptionList>
 )
 datatype AutoScalingSettingsUpdate = | AutoScalingSettingsUpdate (
 nameonly MinimumUnits: Option<PositiveLongObject> ,
 nameonly MaximumUnits: Option<PositiveLongObject> ,
 nameonly AutoScalingDisabled: Option<BooleanObject> ,
 nameonly AutoScalingRoleArn: Option<AutoScalingRoleArn> ,
 nameonly ScalingPolicyUpdate: Option<AutoScalingPolicyUpdate>
 )
 datatype AutoScalingTargetTrackingScalingPolicyConfigurationDescription = | AutoScalingTargetTrackingScalingPolicyConfigurationDescription (
 nameonly DisableScaleIn: Option<BooleanObject> ,
 nameonly ScaleInCooldown: Option<IntegerObject> ,
 nameonly ScaleOutCooldown: Option<IntegerObject> ,
 nameonly TargetValue: Double
 )
 datatype AutoScalingTargetTrackingScalingPolicyConfigurationUpdate = | AutoScalingTargetTrackingScalingPolicyConfigurationUpdate (
 nameonly DisableScaleIn: Option<BooleanObject> ,
 nameonly ScaleInCooldown: Option<IntegerObject> ,
 nameonly ScaleOutCooldown: Option<IntegerObject> ,
 nameonly TargetValue: Double
 )
 type Backfilling = bool
 type BackupArn = x: string | IsValid_BackupArn(x) witness *
 predicate method IsValid_BackupArn(x: string) {
 ( 37 <= |x| <= 1024 )
}
 datatype BackupDescription = | BackupDescription (
 nameonly BackupDetails: Option<BackupDetails> ,
 nameonly SourceTableDetails: Option<SourceTableDetails> ,
 nameonly SourceTableFeatureDetails: Option<SourceTableFeatureDetails>
 )
 datatype BackupDetails = | BackupDetails (
 nameonly BackupArn: BackupArn ,
 nameonly BackupName: BackupName ,
 nameonly BackupSizeBytes: Option<BackupSizeBytes> ,
 nameonly BackupStatus: BackupStatus ,
 nameonly BackupType: BackupType ,
 nameonly BackupCreationDateTime: string ,
 nameonly BackupExpiryDateTime: Option<string>
 )
 type BackupName = x: string | IsValid_BackupName(x) witness *
 predicate method IsValid_BackupName(x: string) {
 ( 3 <= |x| <= 255 )
}
 type BackupsInputLimit = x: int32 | IsValid_BackupsInputLimit(x) witness *
 predicate method IsValid_BackupsInputLimit(x: int32) {
 ( 1 <= x <= 100 )
}
 type BackupSizeBytes = x: int64 | IsValid_BackupSizeBytes(x) witness *
 predicate method IsValid_BackupSizeBytes(x: int64) {
 ( 0 <= x  )
}
 datatype BackupStatus =
	| CREATING
	| DELETED
	| AVAILABLE
 type BackupSummaries = seq<BackupSummary>
 datatype BackupSummary = | BackupSummary (
 nameonly TableName: Option<TableName> ,
 nameonly TableId: Option<TableId> ,
 nameonly TableArn: Option<TableArn> ,
 nameonly BackupArn: Option<BackupArn> ,
 nameonly BackupName: Option<BackupName> ,
 nameonly BackupCreationDateTime: Option<string> ,
 nameonly BackupExpiryDateTime: Option<string> ,
 nameonly BackupStatus: Option<BackupStatus> ,
 nameonly BackupType: Option<BackupType> ,
 nameonly BackupSizeBytes: Option<BackupSizeBytes>
 )
 datatype BackupType =
	| USER
	| SYSTEM
	| AWS_BACKUP
 datatype BackupTypeFilter =
	| USER
	| SYSTEM
	| AWS_BACKUP
	| ALL
 datatype BatchExecuteStatementInput = | BatchExecuteStatementInput (
 nameonly Statements: PartiQLBatchRequest ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity>
 )
 datatype BatchExecuteStatementOutput = | BatchExecuteStatementOutput (
 nameonly Responses: Option<PartiQLBatchResponse> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple>
 )
 datatype BatchGetItemInput = | BatchGetItemInput (
 nameonly RequestItems: BatchGetRequestMap ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity>
 )
 datatype BatchGetItemOutput = | BatchGetItemOutput (
 nameonly Responses: Option<BatchGetResponseMap> ,
 nameonly UnprocessedKeys: Option<BatchGetRequestMap> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple>
 )
 type BatchGetRequestMap = x: map<TableName, KeysAndAttributes> | IsValid_BatchGetRequestMap(x) witness *
 predicate method IsValid_BatchGetRequestMap(x: map<TableName, KeysAndAttributes>) {
 ( 1 <= |x| <= 100 )
}
 type BatchGetResponseMap = map<TableName, ItemList>
 datatype BatchStatementError = | BatchStatementError (
 nameonly Code: Option<BatchStatementErrorCodeEnum> ,
 nameonly Message: Option<String>
 )
 datatype BatchStatementErrorCodeEnum =
	| ConditionalCheckFailed
	| ItemCollectionSizeLimitExceeded
	| RequestLimitExceeded
	| ValidationError
	| ProvisionedThroughputExceeded
	| TransactionConflict
	| ThrottlingError
	| InternalServerError
	| ResourceNotFound
	| AccessDenied
	| DuplicateItem
 datatype BatchStatementRequest = | BatchStatementRequest (
 nameonly Statement: PartiQLStatement ,
 nameonly Parameters: Option<PreparedStatementParameters> ,
 nameonly ConsistentRead: Option<ConsistentRead>
 )
 datatype BatchStatementResponse = | BatchStatementResponse (
 nameonly Error: Option<BatchStatementError> ,
 nameonly TableName: Option<TableName> ,
 nameonly Item: Option<AttributeMap>
 )
 datatype BatchWriteItemInput = | BatchWriteItemInput (
 nameonly RequestItems: BatchWriteItemRequestMap ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics>
 )
 datatype BatchWriteItemOutput = | BatchWriteItemOutput (
 nameonly UnprocessedItems: Option<BatchWriteItemRequestMap> ,
 nameonly ItemCollectionMetrics: Option<ItemCollectionMetricsPerTable> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple>
 )
 type BatchWriteItemRequestMap = x: map<TableName, WriteRequests> | IsValid_BatchWriteItemRequestMap(x) witness *
 predicate method IsValid_BatchWriteItemRequestMap(x: map<TableName, WriteRequests>) {
 ( 1 <= |x| <= 25 )
}
 type BilledSizeBytes = x: int64 | IsValid_BilledSizeBytes(x) witness *
 predicate method IsValid_BilledSizeBytes(x: int64) {
 ( 0 <= x  )
}
 datatype BillingMode =
	| PROVISIONED
	| PAY_PER_REQUEST
 datatype BillingModeSummary = | BillingModeSummary (
 nameonly BillingMode: Option<BillingMode> ,
 nameonly LastUpdateToPayPerRequestDateTime: Option<string>
 )
 type BinaryAttributeValue = seq<uint8>
 type BinarySetAttributeValue = seq<BinaryAttributeValue>
 type BooleanAttributeValue = bool
 type BooleanObject = bool
 datatype CancellationReason = | CancellationReason (
 nameonly Item: Option<AttributeMap> ,
 nameonly Code: Option<Code> ,
 nameonly Message: Option<ErrorMessage>
 )
 type CancellationReasonList = x: seq<CancellationReason> | IsValid_CancellationReasonList(x) witness *
 predicate method IsValid_CancellationReasonList(x: seq<CancellationReason>) {
 ( 1 <= |x| <= 25 )
}
 datatype Capacity = | Capacity (
 nameonly ReadCapacityUnits: Option<ConsumedCapacityUnits> ,
 nameonly WriteCapacityUnits: Option<ConsumedCapacityUnits> ,
 nameonly CapacityUnits: Option<ConsumedCapacityUnits>
 )
 type ClientRequestToken = x: string | IsValid_ClientRequestToken(x) witness *
 predicate method IsValid_ClientRequestToken(x: string) {
 ( 1 <= |x| <= 36 )
}
 type ClientToken = string
 type CloudWatchLogGroupArn = x: string | IsValid_CloudWatchLogGroupArn(x) witness *
 predicate method IsValid_CloudWatchLogGroupArn(x: string) {
 ( 1 <= |x| <= 1024 )
}
 type Code = string
 datatype ComparisonOperator =
	| EQ
	| NE
	| IN
	| LE
	| LT
	| GE
	| GT
	| BETWEEN
	| NOT_NULL
	| NULL
	| CONTAINS
	| NOT_CONTAINS
	| BEGINS_WITH
 datatype Condition = | Condition (
 nameonly AttributeValueList: Option<AttributeValueList> ,
 nameonly ComparisonOperator: ComparisonOperator
 )
 datatype ConditionalOperator =
	| AND
	| OR
 datatype ConditionCheck = | ConditionCheck (
 nameonly Key: Key ,
 nameonly TableName: TableName ,
 nameonly ConditionExpression: ConditionExpression ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> ,
 nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure>
 )
 type ConditionExpression = string
 type ConsistentRead = bool
 datatype ConsumedCapacity = | ConsumedCapacity (
 nameonly TableName: Option<TableName> ,
 nameonly CapacityUnits: Option<ConsumedCapacityUnits> ,
 nameonly ReadCapacityUnits: Option<ConsumedCapacityUnits> ,
 nameonly WriteCapacityUnits: Option<ConsumedCapacityUnits> ,
 nameonly Table: Option<Capacity> ,
 nameonly LocalSecondaryIndexes: Option<SecondaryIndexesCapacityMap> ,
 nameonly GlobalSecondaryIndexes: Option<SecondaryIndexesCapacityMap>
 )
 type ConsumedCapacityMultiple = seq<ConsumedCapacity>
 type ConsumedCapacityUnits = int32
 datatype ContinuousBackupsDescription = | ContinuousBackupsDescription (
 nameonly ContinuousBackupsStatus: ContinuousBackupsStatus ,
 nameonly PointInTimeRecoveryDescription: Option<PointInTimeRecoveryDescription>
 )
 datatype ContinuousBackupsStatus =
	| ENABLED
	| DISABLED
 datatype ContributorInsightsAction =
	| ENABLE
	| DISABLE
 type ContributorInsightsRule = string
 type ContributorInsightsRuleList = seq<ContributorInsightsRule>
 datatype ContributorInsightsStatus =
	| ENABLING
	| ENABLED
	| DISABLING
	| DISABLED
	| FAILED
 type ContributorInsightsSummaries = seq<ContributorInsightsSummary>
 datatype ContributorInsightsSummary = | ContributorInsightsSummary (
 nameonly TableName: Option<TableName> ,
 nameonly IndexName: Option<IndexName> ,
 nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus>
 )
 datatype CreateBackupInput = | CreateBackupInput (
 nameonly TableName: TableName ,
 nameonly BackupName: BackupName
 )
 datatype CreateBackupOutput = | CreateBackupOutput (
 nameonly BackupDetails: Option<BackupDetails>
 )
 datatype CreateGlobalSecondaryIndexAction = | CreateGlobalSecondaryIndexAction (
 nameonly IndexName: IndexName ,
 nameonly KeySchema: KeySchema ,
 nameonly Projection: Projection ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput>
 )
 datatype CreateGlobalTableInput = | CreateGlobalTableInput (
 nameonly GlobalTableName: TableName ,
 nameonly ReplicationGroup: ReplicaList
 )
 datatype CreateGlobalTableOutput = | CreateGlobalTableOutput (
 nameonly GlobalTableDescription: Option<GlobalTableDescription>
 )
 datatype CreateReplicaAction = | CreateReplicaAction (
 nameonly RegionName: RegionName
 )
 datatype CreateReplicationGroupMemberAction = | CreateReplicationGroupMemberAction (
 nameonly RegionName: RegionName ,
 nameonly KMSMasterKeyId: Option<KMSMasterKeyId> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> ,
 nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexList> ,
 nameonly TableClassOverride: Option<TableClass>
 )
 datatype CreateTableInput = | CreateTableInput (
 nameonly AttributeDefinitions: AttributeDefinitions ,
 nameonly TableName: TableName ,
 nameonly KeySchema: KeySchema ,
 nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexList> ,
 nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexList> ,
 nameonly BillingMode: Option<BillingMode> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput> ,
 nameonly StreamSpecification: Option<StreamSpecification> ,
 nameonly SSESpecification: Option<SSESpecification> ,
 nameonly Tags: Option<TagList> ,
 nameonly TableClass: Option<TableClass>
 )
 datatype CreateTableOutput = | CreateTableOutput (
 nameonly TableDescription: Option<TableDescription>
 )
 type CsvDelimiter = x: string | IsValid_CsvDelimiter(x) witness *
 predicate method IsValid_CsvDelimiter(x: string) {
 ( 1 <= |x| <= 1 )
}
 type CsvHeader = x: string | IsValid_CsvHeader(x) witness *
 predicate method IsValid_CsvHeader(x: string) {
 ( 1 <= |x| <= 65536 )
}
 type CsvHeaderList = x: seq<CsvHeader> | IsValid_CsvHeaderList(x) witness *
 predicate method IsValid_CsvHeaderList(x: seq<CsvHeader>) {
 ( 1 <= |x| <= 255 )
}
 datatype CsvOptions = | CsvOptions (
 nameonly Delimiter: Option<CsvDelimiter> ,
 nameonly HeaderList: Option<CsvHeaderList>
 )
 datatype Delete = | Delete (
 nameonly Key: Key ,
 nameonly TableName: TableName ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> ,
 nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure>
 )
 datatype DeleteBackupInput = | DeleteBackupInput (
 nameonly BackupArn: BackupArn
 )
 datatype DeleteBackupOutput = | DeleteBackupOutput (
 nameonly BackupDescription: Option<BackupDescription>
 )
 datatype DeleteGlobalSecondaryIndexAction = | DeleteGlobalSecondaryIndexAction (
 nameonly IndexName: IndexName
 )
 datatype DeleteItemInput = | DeleteItemInput (
 nameonly TableName: TableName ,
 nameonly Key: Key ,
 nameonly Expected: Option<ExpectedAttributeMap> ,
 nameonly ConditionalOperator: Option<ConditionalOperator> ,
 nameonly ReturnValues: Option<ReturnValue> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap>
 )
 datatype DeleteItemOutput = | DeleteItemOutput (
 nameonly Attributes: Option<AttributeMap> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity> ,
 nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics>
 )
 datatype DeleteReplicaAction = | DeleteReplicaAction (
 nameonly RegionName: RegionName
 )
 datatype DeleteReplicationGroupMemberAction = | DeleteReplicationGroupMemberAction (
 nameonly RegionName: RegionName
 )
 datatype DeleteRequest = | DeleteRequest (
 nameonly Key: Key
 )
 datatype DeleteTableInput = | DeleteTableInput (
 nameonly TableName: TableName
 )
 datatype DeleteTableOutput = | DeleteTableOutput (
 nameonly TableDescription: Option<TableDescription>
 )
 datatype DescribeBackupInput = | DescribeBackupInput (
 nameonly BackupArn: BackupArn
 )
 datatype DescribeBackupOutput = | DescribeBackupOutput (
 nameonly BackupDescription: Option<BackupDescription>
 )
 datatype DescribeContinuousBackupsInput = | DescribeContinuousBackupsInput (
 nameonly TableName: TableName
 )
 datatype DescribeContinuousBackupsOutput = | DescribeContinuousBackupsOutput (
 nameonly ContinuousBackupsDescription: Option<ContinuousBackupsDescription>
 )
 datatype DescribeContributorInsightsInput = | DescribeContributorInsightsInput (
 nameonly TableName: TableName ,
 nameonly IndexName: Option<IndexName>
 )
 datatype DescribeContributorInsightsOutput = | DescribeContributorInsightsOutput (
 nameonly TableName: Option<TableName> ,
 nameonly IndexName: Option<IndexName> ,
 nameonly ContributorInsightsRuleList: Option<ContributorInsightsRuleList> ,
 nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus> ,
 nameonly LastUpdateDateTime: Option<string> ,
 nameonly FailureException: Option<FailureException>
 )
 datatype DescribeEndpointsRequest = | DescribeEndpointsRequest (
 
 )
 datatype DescribeEndpointsResponse = | DescribeEndpointsResponse (
 nameonly Endpoints: Endpoints
 )
 datatype DescribeExportInput = | DescribeExportInput (
 nameonly ExportArn: ExportArn
 )
 datatype DescribeExportOutput = | DescribeExportOutput (
 nameonly ExportDescription: Option<ExportDescription>
 )
 datatype DescribeGlobalTableInput = | DescribeGlobalTableInput (
 nameonly GlobalTableName: TableName
 )
 datatype DescribeGlobalTableOutput = | DescribeGlobalTableOutput (
 nameonly GlobalTableDescription: Option<GlobalTableDescription>
 )
 datatype DescribeGlobalTableSettingsInput = | DescribeGlobalTableSettingsInput (
 nameonly GlobalTableName: TableName
 )
 datatype DescribeGlobalTableSettingsOutput = | DescribeGlobalTableSettingsOutput (
 nameonly GlobalTableName: Option<TableName> ,
 nameonly ReplicaSettings: Option<ReplicaSettingsDescriptionList>
 )
 datatype DescribeImportInput = | DescribeImportInput (
 nameonly ImportArn: ImportArn
 )
 datatype DescribeImportOutput = | DescribeImportOutput (
 nameonly ImportTableDescription: ImportTableDescription
 )
 datatype DescribeKinesisStreamingDestinationInput = | DescribeKinesisStreamingDestinationInput (
 nameonly TableName: TableName
 )
 datatype DescribeKinesisStreamingDestinationOutput = | DescribeKinesisStreamingDestinationOutput (
 nameonly TableName: Option<TableName> ,
 nameonly KinesisDataStreamDestinations: Option<KinesisDataStreamDestinations>
 )
 datatype DescribeLimitsInput = | DescribeLimitsInput (
 
 )
 datatype DescribeLimitsOutput = | DescribeLimitsOutput (
 nameonly AccountMaxReadCapacityUnits: Option<PositiveLongObject> ,
 nameonly AccountMaxWriteCapacityUnits: Option<PositiveLongObject> ,
 nameonly TableMaxReadCapacityUnits: Option<PositiveLongObject> ,
 nameonly TableMaxWriteCapacityUnits: Option<PositiveLongObject>
 )
 datatype DescribeTableInput = | DescribeTableInput (
 nameonly TableName: TableName
 )
 datatype DescribeTableOutput = | DescribeTableOutput (
 nameonly Table: Option<TableDescription>
 )
 datatype DescribeTableReplicaAutoScalingInput = | DescribeTableReplicaAutoScalingInput (
 nameonly TableName: TableName
 )
 datatype DescribeTableReplicaAutoScalingOutput = | DescribeTableReplicaAutoScalingOutput (
 nameonly TableAutoScalingDescription: Option<TableAutoScalingDescription>
 )
 datatype DescribeTimeToLiveInput = | DescribeTimeToLiveInput (
 nameonly TableName: TableName
 )
 datatype DescribeTimeToLiveOutput = | DescribeTimeToLiveOutput (
 nameonly TimeToLiveDescription: Option<TimeToLiveDescription>
 )
 datatype DestinationStatus =
	| ENABLING
	| ACTIVE
	| DISABLING
	| DISABLED
	| ENABLE_FAILED
 datatype DisableKinesisStreamingDestinationInput = | DisableKinesisStreamingDestinationInput (
 nameonly TableName: TableName ,
 nameonly StreamArn: StreamArn
 )
 datatype DisableKinesisStreamingDestinationOutput = | DisableKinesisStreamingDestinationOutput (
 nameonly TableName: Option<TableName> ,
 nameonly StreamArn: Option<StreamArn> ,
 nameonly DestinationStatus: Option<DestinationStatus>
 )
 type Double = int32
 class IDynamoDB_20120810ClientCallHistory {
 ghost constructor() {
 BatchExecuteStatement := [];
 BatchGetItem := [];
 BatchWriteItem := [];
 CreateBackup := [];
 CreateGlobalTable := [];
 CreateTable := [];
 DeleteBackup := [];
 DeleteItem := [];
 DeleteTable := [];
 DescribeBackup := [];
 DescribeContinuousBackups := [];
 DescribeContributorInsights := [];
 DescribeEndpoints := [];
 DescribeExport := [];
 DescribeGlobalTable := [];
 DescribeGlobalTableSettings := [];
 DescribeImport := [];
 DescribeKinesisStreamingDestination := [];
 DescribeLimits := [];
 DescribeTable := [];
 DescribeTableReplicaAutoScaling := [];
 DescribeTimeToLive := [];
 DisableKinesisStreamingDestination := [];
 EnableKinesisStreamingDestination := [];
 ExecuteStatement := [];
 ExecuteTransaction := [];
 ExportTableToPointInTime := [];
 GetItem := [];
 ImportTable := [];
 ListBackups := [];
 ListContributorInsights := [];
 ListExports := [];
 ListGlobalTables := [];
 ListImports := [];
 ListTables := [];
 ListTagsOfResource := [];
 PutItem := [];
 Query := [];
 RestoreTableFromBackup := [];
 RestoreTableToPointInTime := [];
 Scan := [];
 TagResource := [];
 TransactGetItems := [];
 TransactWriteItems := [];
 UntagResource := [];
 UpdateContinuousBackups := [];
 UpdateContributorInsights := [];
 UpdateGlobalTable := [];
 UpdateGlobalTableSettings := [];
 UpdateItem := [];
 UpdateTable := [];
 UpdateTableReplicaAutoScaling := [];
 UpdateTimeToLive := [];
}
 ghost var BatchExecuteStatement: seq<DafnyCallEvent<BatchExecuteStatementInput, Result<BatchExecuteStatementOutput, Error>>>
 ghost var BatchGetItem: seq<DafnyCallEvent<BatchGetItemInput, Result<BatchGetItemOutput, Error>>>
 ghost var BatchWriteItem: seq<DafnyCallEvent<BatchWriteItemInput, Result<BatchWriteItemOutput, Error>>>
 ghost var CreateBackup: seq<DafnyCallEvent<CreateBackupInput, Result<CreateBackupOutput, Error>>>
 ghost var CreateGlobalTable: seq<DafnyCallEvent<CreateGlobalTableInput, Result<CreateGlobalTableOutput, Error>>>
 ghost var CreateTable: seq<DafnyCallEvent<CreateTableInput, Result<CreateTableOutput, Error>>>
 ghost var DeleteBackup: seq<DafnyCallEvent<DeleteBackupInput, Result<DeleteBackupOutput, Error>>>
 ghost var DeleteItem: seq<DafnyCallEvent<DeleteItemInput, Result<DeleteItemOutput, Error>>>
 ghost var DeleteTable: seq<DafnyCallEvent<DeleteTableInput, Result<DeleteTableOutput, Error>>>
 ghost var DescribeBackup: seq<DafnyCallEvent<DescribeBackupInput, Result<DescribeBackupOutput, Error>>>
 ghost var DescribeContinuousBackups: seq<DafnyCallEvent<DescribeContinuousBackupsInput, Result<DescribeContinuousBackupsOutput, Error>>>
 ghost var DescribeContributorInsights: seq<DafnyCallEvent<DescribeContributorInsightsInput, Result<DescribeContributorInsightsOutput, Error>>>
 ghost var DescribeEndpoints: seq<DafnyCallEvent<DescribeEndpointsRequest, Result<DescribeEndpointsResponse, Error>>>
 ghost var DescribeExport: seq<DafnyCallEvent<DescribeExportInput, Result<DescribeExportOutput, Error>>>
 ghost var DescribeGlobalTable: seq<DafnyCallEvent<DescribeGlobalTableInput, Result<DescribeGlobalTableOutput, Error>>>
 ghost var DescribeGlobalTableSettings: seq<DafnyCallEvent<DescribeGlobalTableSettingsInput, Result<DescribeGlobalTableSettingsOutput, Error>>>
 ghost var DescribeImport: seq<DafnyCallEvent<DescribeImportInput, Result<DescribeImportOutput, Error>>>
 ghost var DescribeKinesisStreamingDestination: seq<DafnyCallEvent<DescribeKinesisStreamingDestinationInput, Result<DescribeKinesisStreamingDestinationOutput, Error>>>
 ghost var DescribeLimits: seq<DafnyCallEvent<DescribeLimitsInput, Result<DescribeLimitsOutput, Error>>>
 ghost var DescribeTable: seq<DafnyCallEvent<DescribeTableInput, Result<DescribeTableOutput, Error>>>
 ghost var DescribeTableReplicaAutoScaling: seq<DafnyCallEvent<DescribeTableReplicaAutoScalingInput, Result<DescribeTableReplicaAutoScalingOutput, Error>>>
 ghost var DescribeTimeToLive: seq<DafnyCallEvent<DescribeTimeToLiveInput, Result<DescribeTimeToLiveOutput, Error>>>
 ghost var DisableKinesisStreamingDestination: seq<DafnyCallEvent<DisableKinesisStreamingDestinationInput, Result<DisableKinesisStreamingDestinationOutput, Error>>>
 ghost var EnableKinesisStreamingDestination: seq<DafnyCallEvent<EnableKinesisStreamingDestinationInput, Result<EnableKinesisStreamingDestinationOutput, Error>>>
 ghost var ExecuteStatement: seq<DafnyCallEvent<ExecuteStatementInput, Result<ExecuteStatementOutput, Error>>>
 ghost var ExecuteTransaction: seq<DafnyCallEvent<ExecuteTransactionInput, Result<ExecuteTransactionOutput, Error>>>
 ghost var ExportTableToPointInTime: seq<DafnyCallEvent<ExportTableToPointInTimeInput, Result<ExportTableToPointInTimeOutput, Error>>>
 ghost var GetItem: seq<DafnyCallEvent<GetItemInput, Result<GetItemOutput, Error>>>
 ghost var ImportTable: seq<DafnyCallEvent<ImportTableInput, Result<ImportTableOutput, Error>>>
 ghost var ListBackups: seq<DafnyCallEvent<ListBackupsInput, Result<ListBackupsOutput, Error>>>
 ghost var ListContributorInsights: seq<DafnyCallEvent<ListContributorInsightsInput, Result<ListContributorInsightsOutput, Error>>>
 ghost var ListExports: seq<DafnyCallEvent<ListExportsInput, Result<ListExportsOutput, Error>>>
 ghost var ListGlobalTables: seq<DafnyCallEvent<ListGlobalTablesInput, Result<ListGlobalTablesOutput, Error>>>
 ghost var ListImports: seq<DafnyCallEvent<ListImportsInput, Result<ListImportsOutput, Error>>>
 ghost var ListTables: seq<DafnyCallEvent<ListTablesInput, Result<ListTablesOutput, Error>>>
 ghost var ListTagsOfResource: seq<DafnyCallEvent<ListTagsOfResourceInput, Result<ListTagsOfResourceOutput, Error>>>
 ghost var PutItem: seq<DafnyCallEvent<PutItemInput, Result<PutItemOutput, Error>>>
 ghost var Query: seq<DafnyCallEvent<QueryInput, Result<QueryOutput, Error>>>
 ghost var RestoreTableFromBackup: seq<DafnyCallEvent<RestoreTableFromBackupInput, Result<RestoreTableFromBackupOutput, Error>>>
 ghost var RestoreTableToPointInTime: seq<DafnyCallEvent<RestoreTableToPointInTimeInput, Result<RestoreTableToPointInTimeOutput, Error>>>
 ghost var Scan: seq<DafnyCallEvent<ScanInput, Result<ScanOutput, Error>>>
 ghost var TagResource: seq<DafnyCallEvent<TagResourceInput, Result<(), Error>>>
 ghost var TransactGetItems: seq<DafnyCallEvent<TransactGetItemsInput, Result<TransactGetItemsOutput, Error>>>
 ghost var TransactWriteItems: seq<DafnyCallEvent<TransactWriteItemsInput, Result<TransactWriteItemsOutput, Error>>>
 ghost var UntagResource: seq<DafnyCallEvent<UntagResourceInput, Result<(), Error>>>
 ghost var UpdateContinuousBackups: seq<DafnyCallEvent<UpdateContinuousBackupsInput, Result<UpdateContinuousBackupsOutput, Error>>>
 ghost var UpdateContributorInsights: seq<DafnyCallEvent<UpdateContributorInsightsInput, Result<UpdateContributorInsightsOutput, Error>>>
 ghost var UpdateGlobalTable: seq<DafnyCallEvent<UpdateGlobalTableInput, Result<UpdateGlobalTableOutput, Error>>>
 ghost var UpdateGlobalTableSettings: seq<DafnyCallEvent<UpdateGlobalTableSettingsInput, Result<UpdateGlobalTableSettingsOutput, Error>>>
 ghost var UpdateItem: seq<DafnyCallEvent<UpdateItemInput, Result<UpdateItemOutput, Error>>>
 ghost var UpdateTable: seq<DafnyCallEvent<UpdateTableInput, Result<UpdateTableOutput, Error>>>
 ghost var UpdateTableReplicaAutoScaling: seq<DafnyCallEvent<UpdateTableReplicaAutoScalingInput, Result<UpdateTableReplicaAutoScalingOutput, Error>>>
 ghost var UpdateTimeToLive: seq<DafnyCallEvent<UpdateTimeToLiveInput, Result<UpdateTimeToLiveOutput, Error>>>
}
 trait {:termination false} IDynamoDB_20120810Client
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IDynamoDB_20120810ClientCallHistory
 predicate BatchExecuteStatementEnsuresPublicly(input: BatchExecuteStatementInput , output: Result<BatchExecuteStatementOutput, Error>)
 // The public method to be called by library consumers
 method BatchExecuteStatement ( input: BatchExecuteStatementInput )
 returns (output: Result<BatchExecuteStatementOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`BatchExecuteStatement
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures BatchExecuteStatementEnsuresPublicly(input, output)
 ensures History.BatchExecuteStatement == old(History.BatchExecuteStatement) + [DafnyCallEvent(input, output)]
 
 predicate BatchGetItemEnsuresPublicly(input: BatchGetItemInput , output: Result<BatchGetItemOutput, Error>)
 // The public method to be called by library consumers
 method BatchGetItem ( input: BatchGetItemInput )
 returns (output: Result<BatchGetItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`BatchGetItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures BatchGetItemEnsuresPublicly(input, output)
 ensures History.BatchGetItem == old(History.BatchGetItem) + [DafnyCallEvent(input, output)]
 
 predicate BatchWriteItemEnsuresPublicly(input: BatchWriteItemInput , output: Result<BatchWriteItemOutput, Error>)
 // The public method to be called by library consumers
 method BatchWriteItem ( input: BatchWriteItemInput )
 returns (output: Result<BatchWriteItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`BatchWriteItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures BatchWriteItemEnsuresPublicly(input, output)
 ensures History.BatchWriteItem == old(History.BatchWriteItem) + [DafnyCallEvent(input, output)]
 
 predicate CreateBackupEnsuresPublicly(input: CreateBackupInput , output: Result<CreateBackupOutput, Error>)
 // The public method to be called by library consumers
 method CreateBackup ( input: CreateBackupInput )
 returns (output: Result<CreateBackupOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateBackup
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures CreateBackupEnsuresPublicly(input, output)
 ensures History.CreateBackup == old(History.CreateBackup) + [DafnyCallEvent(input, output)]
 
 predicate CreateGlobalTableEnsuresPublicly(input: CreateGlobalTableInput , output: Result<CreateGlobalTableOutput, Error>)
 // The public method to be called by library consumers
 method CreateGlobalTable ( input: CreateGlobalTableInput )
 returns (output: Result<CreateGlobalTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateGlobalTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures CreateGlobalTableEnsuresPublicly(input, output)
 ensures History.CreateGlobalTable == old(History.CreateGlobalTable) + [DafnyCallEvent(input, output)]
 
 predicate CreateTableEnsuresPublicly(input: CreateTableInput , output: Result<CreateTableOutput, Error>)
 // The public method to be called by library consumers
 method CreateTable ( input: CreateTableInput )
 returns (output: Result<CreateTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures CreateTableEnsuresPublicly(input, output)
 ensures History.CreateTable == old(History.CreateTable) + [DafnyCallEvent(input, output)]
 
 predicate DeleteBackupEnsuresPublicly(input: DeleteBackupInput , output: Result<DeleteBackupOutput, Error>)
 // The public method to be called by library consumers
 method DeleteBackup ( input: DeleteBackupInput )
 returns (output: Result<DeleteBackupOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DeleteBackup
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DeleteBackupEnsuresPublicly(input, output)
 ensures History.DeleteBackup == old(History.DeleteBackup) + [DafnyCallEvent(input, output)]
 
 predicate DeleteItemEnsuresPublicly(input: DeleteItemInput , output: Result<DeleteItemOutput, Error>)
 // The public method to be called by library consumers
 method DeleteItem ( input: DeleteItemInput )
 returns (output: Result<DeleteItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DeleteItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DeleteItemEnsuresPublicly(input, output)
 ensures History.DeleteItem == old(History.DeleteItem) + [DafnyCallEvent(input, output)]
 
 predicate DeleteTableEnsuresPublicly(input: DeleteTableInput , output: Result<DeleteTableOutput, Error>)
 // The public method to be called by library consumers
 method DeleteTable ( input: DeleteTableInput )
 returns (output: Result<DeleteTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DeleteTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DeleteTableEnsuresPublicly(input, output)
 ensures History.DeleteTable == old(History.DeleteTable) + [DafnyCallEvent(input, output)]
 
 predicate DescribeBackupEnsuresPublicly(input: DescribeBackupInput , output: Result<DescribeBackupOutput, Error>)
 // The public method to be called by library consumers
 method DescribeBackup ( input: DescribeBackupInput )
 returns (output: Result<DescribeBackupOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeBackup
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeBackupEnsuresPublicly(input, output)
 ensures History.DescribeBackup == old(History.DescribeBackup) + [DafnyCallEvent(input, output)]
 
 predicate DescribeContinuousBackupsEnsuresPublicly(input: DescribeContinuousBackupsInput , output: Result<DescribeContinuousBackupsOutput, Error>)
 // The public method to be called by library consumers
 method DescribeContinuousBackups ( input: DescribeContinuousBackupsInput )
 returns (output: Result<DescribeContinuousBackupsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeContinuousBackups
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeContinuousBackupsEnsuresPublicly(input, output)
 ensures History.DescribeContinuousBackups == old(History.DescribeContinuousBackups) + [DafnyCallEvent(input, output)]
 
 predicate DescribeContributorInsightsEnsuresPublicly(input: DescribeContributorInsightsInput , output: Result<DescribeContributorInsightsOutput, Error>)
 // The public method to be called by library consumers
 method DescribeContributorInsights ( input: DescribeContributorInsightsInput )
 returns (output: Result<DescribeContributorInsightsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeContributorInsights
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeContributorInsightsEnsuresPublicly(input, output)
 ensures History.DescribeContributorInsights == old(History.DescribeContributorInsights) + [DafnyCallEvent(input, output)]
 
 predicate DescribeEndpointsEnsuresPublicly(input: DescribeEndpointsRequest , output: Result<DescribeEndpointsResponse, Error>)
 // The public method to be called by library consumers
 method DescribeEndpoints ( input: DescribeEndpointsRequest )
 returns (output: Result<DescribeEndpointsResponse, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeEndpoints
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeEndpointsEnsuresPublicly(input, output)
 ensures History.DescribeEndpoints == old(History.DescribeEndpoints) + [DafnyCallEvent(input, output)]
 
 predicate DescribeExportEnsuresPublicly(input: DescribeExportInput , output: Result<DescribeExportOutput, Error>)
 // The public method to be called by library consumers
 method DescribeExport ( input: DescribeExportInput )
 returns (output: Result<DescribeExportOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeExport
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeExportEnsuresPublicly(input, output)
 ensures History.DescribeExport == old(History.DescribeExport) + [DafnyCallEvent(input, output)]
 
 predicate DescribeGlobalTableEnsuresPublicly(input: DescribeGlobalTableInput , output: Result<DescribeGlobalTableOutput, Error>)
 // The public method to be called by library consumers
 method DescribeGlobalTable ( input: DescribeGlobalTableInput )
 returns (output: Result<DescribeGlobalTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeGlobalTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeGlobalTableEnsuresPublicly(input, output)
 ensures History.DescribeGlobalTable == old(History.DescribeGlobalTable) + [DafnyCallEvent(input, output)]
 
 predicate DescribeGlobalTableSettingsEnsuresPublicly(input: DescribeGlobalTableSettingsInput , output: Result<DescribeGlobalTableSettingsOutput, Error>)
 // The public method to be called by library consumers
 method DescribeGlobalTableSettings ( input: DescribeGlobalTableSettingsInput )
 returns (output: Result<DescribeGlobalTableSettingsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeGlobalTableSettings
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeGlobalTableSettingsEnsuresPublicly(input, output)
 ensures History.DescribeGlobalTableSettings == old(History.DescribeGlobalTableSettings) + [DafnyCallEvent(input, output)]
 
 predicate DescribeImportEnsuresPublicly(input: DescribeImportInput , output: Result<DescribeImportOutput, Error>)
 // The public method to be called by library consumers
 method DescribeImport ( input: DescribeImportInput )
 returns (output: Result<DescribeImportOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeImport
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeImportEnsuresPublicly(input, output)
 ensures History.DescribeImport == old(History.DescribeImport) + [DafnyCallEvent(input, output)]
 
 predicate DescribeKinesisStreamingDestinationEnsuresPublicly(input: DescribeKinesisStreamingDestinationInput , output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
 // The public method to be called by library consumers
 method DescribeKinesisStreamingDestination ( input: DescribeKinesisStreamingDestinationInput )
 returns (output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeKinesisStreamingDestination
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeKinesisStreamingDestinationEnsuresPublicly(input, output)
 ensures History.DescribeKinesisStreamingDestination == old(History.DescribeKinesisStreamingDestination) + [DafnyCallEvent(input, output)]
 
 predicate DescribeLimitsEnsuresPublicly(input: DescribeLimitsInput , output: Result<DescribeLimitsOutput, Error>)
 // The public method to be called by library consumers
 method DescribeLimits ( input: DescribeLimitsInput )
 returns (output: Result<DescribeLimitsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeLimits
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeLimitsEnsuresPublicly(input, output)
 ensures History.DescribeLimits == old(History.DescribeLimits) + [DafnyCallEvent(input, output)]
 
 predicate DescribeTableEnsuresPublicly(input: DescribeTableInput , output: Result<DescribeTableOutput, Error>)
 // The public method to be called by library consumers
 method DescribeTable ( input: DescribeTableInput )
 returns (output: Result<DescribeTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeTableEnsuresPublicly(input, output)
 ensures History.DescribeTable == old(History.DescribeTable) + [DafnyCallEvent(input, output)]
 
 predicate DescribeTableReplicaAutoScalingEnsuresPublicly(input: DescribeTableReplicaAutoScalingInput , output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
 // The public method to be called by library consumers
 method DescribeTableReplicaAutoScaling ( input: DescribeTableReplicaAutoScalingInput )
 returns (output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeTableReplicaAutoScaling
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeTableReplicaAutoScalingEnsuresPublicly(input, output)
 ensures History.DescribeTableReplicaAutoScaling == old(History.DescribeTableReplicaAutoScaling) + [DafnyCallEvent(input, output)]
 
 predicate DescribeTimeToLiveEnsuresPublicly(input: DescribeTimeToLiveInput , output: Result<DescribeTimeToLiveOutput, Error>)
 // The public method to be called by library consumers
 method DescribeTimeToLive ( input: DescribeTimeToLiveInput )
 returns (output: Result<DescribeTimeToLiveOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DescribeTimeToLive
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DescribeTimeToLiveEnsuresPublicly(input, output)
 ensures History.DescribeTimeToLive == old(History.DescribeTimeToLive) + [DafnyCallEvent(input, output)]
 
 predicate DisableKinesisStreamingDestinationEnsuresPublicly(input: DisableKinesisStreamingDestinationInput , output: Result<DisableKinesisStreamingDestinationOutput, Error>)
 // The public method to be called by library consumers
 method DisableKinesisStreamingDestination ( input: DisableKinesisStreamingDestinationInput )
 returns (output: Result<DisableKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DisableKinesisStreamingDestination
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DisableKinesisStreamingDestinationEnsuresPublicly(input, output)
 ensures History.DisableKinesisStreamingDestination == old(History.DisableKinesisStreamingDestination) + [DafnyCallEvent(input, output)]
 
 predicate EnableKinesisStreamingDestinationEnsuresPublicly(input: EnableKinesisStreamingDestinationInput , output: Result<EnableKinesisStreamingDestinationOutput, Error>)
 // The public method to be called by library consumers
 method EnableKinesisStreamingDestination ( input: EnableKinesisStreamingDestinationInput )
 returns (output: Result<EnableKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`EnableKinesisStreamingDestination
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures EnableKinesisStreamingDestinationEnsuresPublicly(input, output)
 ensures History.EnableKinesisStreamingDestination == old(History.EnableKinesisStreamingDestination) + [DafnyCallEvent(input, output)]
 
 predicate ExecuteStatementEnsuresPublicly(input: ExecuteStatementInput , output: Result<ExecuteStatementOutput, Error>)
 // The public method to be called by library consumers
 method ExecuteStatement ( input: ExecuteStatementInput )
 returns (output: Result<ExecuteStatementOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ExecuteStatement
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ExecuteStatementEnsuresPublicly(input, output)
 ensures History.ExecuteStatement == old(History.ExecuteStatement) + [DafnyCallEvent(input, output)]
 
 predicate ExecuteTransactionEnsuresPublicly(input: ExecuteTransactionInput , output: Result<ExecuteTransactionOutput, Error>)
 // The public method to be called by library consumers
 method ExecuteTransaction ( input: ExecuteTransactionInput )
 returns (output: Result<ExecuteTransactionOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ExecuteTransaction
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ExecuteTransactionEnsuresPublicly(input, output)
 ensures History.ExecuteTransaction == old(History.ExecuteTransaction) + [DafnyCallEvent(input, output)]
 
 predicate ExportTableToPointInTimeEnsuresPublicly(input: ExportTableToPointInTimeInput , output: Result<ExportTableToPointInTimeOutput, Error>)
 // The public method to be called by library consumers
 method ExportTableToPointInTime ( input: ExportTableToPointInTimeInput )
 returns (output: Result<ExportTableToPointInTimeOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ExportTableToPointInTime
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ExportTableToPointInTimeEnsuresPublicly(input, output)
 ensures History.ExportTableToPointInTime == old(History.ExportTableToPointInTime) + [DafnyCallEvent(input, output)]
 
 predicate GetItemEnsuresPublicly(input: GetItemInput , output: Result<GetItemOutput, Error>)
 // The public method to be called by library consumers
 method GetItem ( input: GetItemInput )
 returns (output: Result<GetItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetItemEnsuresPublicly(input, output)
 ensures History.GetItem == old(History.GetItem) + [DafnyCallEvent(input, output)]
 
 predicate ImportTableEnsuresPublicly(input: ImportTableInput , output: Result<ImportTableOutput, Error>)
 // The public method to be called by library consumers
 method ImportTable ( input: ImportTableInput )
 returns (output: Result<ImportTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ImportTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ImportTableEnsuresPublicly(input, output)
 ensures History.ImportTable == old(History.ImportTable) + [DafnyCallEvent(input, output)]
 
 predicate ListBackupsEnsuresPublicly(input: ListBackupsInput , output: Result<ListBackupsOutput, Error>)
 // The public method to be called by library consumers
 method ListBackups ( input: ListBackupsInput )
 returns (output: Result<ListBackupsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListBackups
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListBackupsEnsuresPublicly(input, output)
 ensures History.ListBackups == old(History.ListBackups) + [DafnyCallEvent(input, output)]
 
 predicate ListContributorInsightsEnsuresPublicly(input: ListContributorInsightsInput , output: Result<ListContributorInsightsOutput, Error>)
 // The public method to be called by library consumers
 method ListContributorInsights ( input: ListContributorInsightsInput )
 returns (output: Result<ListContributorInsightsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListContributorInsights
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListContributorInsightsEnsuresPublicly(input, output)
 ensures History.ListContributorInsights == old(History.ListContributorInsights) + [DafnyCallEvent(input, output)]
 
 predicate ListExportsEnsuresPublicly(input: ListExportsInput , output: Result<ListExportsOutput, Error>)
 // The public method to be called by library consumers
 method ListExports ( input: ListExportsInput )
 returns (output: Result<ListExportsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListExports
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListExportsEnsuresPublicly(input, output)
 ensures History.ListExports == old(History.ListExports) + [DafnyCallEvent(input, output)]
 
 predicate ListGlobalTablesEnsuresPublicly(input: ListGlobalTablesInput , output: Result<ListGlobalTablesOutput, Error>)
 // The public method to be called by library consumers
 method ListGlobalTables ( input: ListGlobalTablesInput )
 returns (output: Result<ListGlobalTablesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListGlobalTables
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListGlobalTablesEnsuresPublicly(input, output)
 ensures History.ListGlobalTables == old(History.ListGlobalTables) + [DafnyCallEvent(input, output)]
 
 predicate ListImportsEnsuresPublicly(input: ListImportsInput , output: Result<ListImportsOutput, Error>)
 // The public method to be called by library consumers
 method ListImports ( input: ListImportsInput )
 returns (output: Result<ListImportsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListImports
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListImportsEnsuresPublicly(input, output)
 ensures History.ListImports == old(History.ListImports) + [DafnyCallEvent(input, output)]
 
 predicate ListTablesEnsuresPublicly(input: ListTablesInput , output: Result<ListTablesOutput, Error>)
 // The public method to be called by library consumers
 method ListTables ( input: ListTablesInput )
 returns (output: Result<ListTablesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListTables
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListTablesEnsuresPublicly(input, output)
 ensures History.ListTables == old(History.ListTables) + [DafnyCallEvent(input, output)]
 
 predicate ListTagsOfResourceEnsuresPublicly(input: ListTagsOfResourceInput , output: Result<ListTagsOfResourceOutput, Error>)
 // The public method to be called by library consumers
 method ListTagsOfResource ( input: ListTagsOfResourceInput )
 returns (output: Result<ListTagsOfResourceOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ListTagsOfResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ListTagsOfResourceEnsuresPublicly(input, output)
 ensures History.ListTagsOfResource == old(History.ListTagsOfResource) + [DafnyCallEvent(input, output)]
 
 predicate PutItemEnsuresPublicly(input: PutItemInput , output: Result<PutItemOutput, Error>)
 // The public method to be called by library consumers
 method PutItem ( input: PutItemInput )
 returns (output: Result<PutItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`PutItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures PutItemEnsuresPublicly(input, output)
 ensures History.PutItem == old(History.PutItem) + [DafnyCallEvent(input, output)]
 
 predicate QueryEnsuresPublicly(input: QueryInput , output: Result<QueryOutput, Error>)
 // The public method to be called by library consumers
 method Query ( input: QueryInput )
 returns (output: Result<QueryOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Query
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures QueryEnsuresPublicly(input, output)
 ensures History.Query == old(History.Query) + [DafnyCallEvent(input, output)]
 
 predicate RestoreTableFromBackupEnsuresPublicly(input: RestoreTableFromBackupInput , output: Result<RestoreTableFromBackupOutput, Error>)
 // The public method to be called by library consumers
 method RestoreTableFromBackup ( input: RestoreTableFromBackupInput )
 returns (output: Result<RestoreTableFromBackupOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RestoreTableFromBackup
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RestoreTableFromBackupEnsuresPublicly(input, output)
 ensures History.RestoreTableFromBackup == old(History.RestoreTableFromBackup) + [DafnyCallEvent(input, output)]
 
 predicate RestoreTableToPointInTimeEnsuresPublicly(input: RestoreTableToPointInTimeInput , output: Result<RestoreTableToPointInTimeOutput, Error>)
 // The public method to be called by library consumers
 method RestoreTableToPointInTime ( input: RestoreTableToPointInTimeInput )
 returns (output: Result<RestoreTableToPointInTimeOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RestoreTableToPointInTime
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RestoreTableToPointInTimeEnsuresPublicly(input, output)
 ensures History.RestoreTableToPointInTime == old(History.RestoreTableToPointInTime) + [DafnyCallEvent(input, output)]
 
 predicate ScanEnsuresPublicly(input: ScanInput , output: Result<ScanOutput, Error>)
 // The public method to be called by library consumers
 method Scan ( input: ScanInput )
 returns (output: Result<ScanOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Scan
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ScanEnsuresPublicly(input, output)
 ensures History.Scan == old(History.Scan) + [DafnyCallEvent(input, output)]
 
 predicate TagResourceEnsuresPublicly(input: TagResourceInput , output: Result<(), Error>)
 // The public method to be called by library consumers
 method TagResource ( input: TagResourceInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`TagResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures TagResourceEnsuresPublicly(input, output)
 ensures History.TagResource == old(History.TagResource) + [DafnyCallEvent(input, output)]
 
 predicate TransactGetItemsEnsuresPublicly(input: TransactGetItemsInput , output: Result<TransactGetItemsOutput, Error>)
 // The public method to be called by library consumers
 method TransactGetItems ( input: TransactGetItemsInput )
 returns (output: Result<TransactGetItemsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`TransactGetItems
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures TransactGetItemsEnsuresPublicly(input, output)
 ensures History.TransactGetItems == old(History.TransactGetItems) + [DafnyCallEvent(input, output)]
 
 predicate TransactWriteItemsEnsuresPublicly(input: TransactWriteItemsInput , output: Result<TransactWriteItemsOutput, Error>)
 // The public method to be called by library consumers
 method TransactWriteItems ( input: TransactWriteItemsInput )
 returns (output: Result<TransactWriteItemsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`TransactWriteItems
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures TransactWriteItemsEnsuresPublicly(input, output)
 ensures History.TransactWriteItems == old(History.TransactWriteItems) + [DafnyCallEvent(input, output)]
 
 predicate UntagResourceEnsuresPublicly(input: UntagResourceInput , output: Result<(), Error>)
 // The public method to be called by library consumers
 method UntagResource ( input: UntagResourceInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UntagResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UntagResourceEnsuresPublicly(input, output)
 ensures History.UntagResource == old(History.UntagResource) + [DafnyCallEvent(input, output)]
 
 predicate UpdateContinuousBackupsEnsuresPublicly(input: UpdateContinuousBackupsInput , output: Result<UpdateContinuousBackupsOutput, Error>)
 // The public method to be called by library consumers
 method UpdateContinuousBackups ( input: UpdateContinuousBackupsInput )
 returns (output: Result<UpdateContinuousBackupsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateContinuousBackups
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateContinuousBackupsEnsuresPublicly(input, output)
 ensures History.UpdateContinuousBackups == old(History.UpdateContinuousBackups) + [DafnyCallEvent(input, output)]
 
 predicate UpdateContributorInsightsEnsuresPublicly(input: UpdateContributorInsightsInput , output: Result<UpdateContributorInsightsOutput, Error>)
 // The public method to be called by library consumers
 method UpdateContributorInsights ( input: UpdateContributorInsightsInput )
 returns (output: Result<UpdateContributorInsightsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateContributorInsights
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateContributorInsightsEnsuresPublicly(input, output)
 ensures History.UpdateContributorInsights == old(History.UpdateContributorInsights) + [DafnyCallEvent(input, output)]
 
 predicate UpdateGlobalTableEnsuresPublicly(input: UpdateGlobalTableInput , output: Result<UpdateGlobalTableOutput, Error>)
 // The public method to be called by library consumers
 method UpdateGlobalTable ( input: UpdateGlobalTableInput )
 returns (output: Result<UpdateGlobalTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateGlobalTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateGlobalTableEnsuresPublicly(input, output)
 ensures History.UpdateGlobalTable == old(History.UpdateGlobalTable) + [DafnyCallEvent(input, output)]
 
 predicate UpdateGlobalTableSettingsEnsuresPublicly(input: UpdateGlobalTableSettingsInput , output: Result<UpdateGlobalTableSettingsOutput, Error>)
 // The public method to be called by library consumers
 method UpdateGlobalTableSettings ( input: UpdateGlobalTableSettingsInput )
 returns (output: Result<UpdateGlobalTableSettingsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateGlobalTableSettings
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateGlobalTableSettingsEnsuresPublicly(input, output)
 ensures History.UpdateGlobalTableSettings == old(History.UpdateGlobalTableSettings) + [DafnyCallEvent(input, output)]
 
 predicate UpdateItemEnsuresPublicly(input: UpdateItemInput , output: Result<UpdateItemOutput, Error>)
 // The public method to be called by library consumers
 method UpdateItem ( input: UpdateItemInput )
 returns (output: Result<UpdateItemOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateItem
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateItemEnsuresPublicly(input, output)
 ensures History.UpdateItem == old(History.UpdateItem) + [DafnyCallEvent(input, output)]
 
 predicate UpdateTableEnsuresPublicly(input: UpdateTableInput , output: Result<UpdateTableOutput, Error>)
 // The public method to be called by library consumers
 method UpdateTable ( input: UpdateTableInput )
 returns (output: Result<UpdateTableOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateTable
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateTableEnsuresPublicly(input, output)
 ensures History.UpdateTable == old(History.UpdateTable) + [DafnyCallEvent(input, output)]
 
 predicate UpdateTableReplicaAutoScalingEnsuresPublicly(input: UpdateTableReplicaAutoScalingInput , output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
 // The public method to be called by library consumers
 method UpdateTableReplicaAutoScaling ( input: UpdateTableReplicaAutoScalingInput )
 returns (output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateTableReplicaAutoScaling
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateTableReplicaAutoScalingEnsuresPublicly(input, output)
 ensures History.UpdateTableReplicaAutoScaling == old(History.UpdateTableReplicaAutoScaling) + [DafnyCallEvent(input, output)]
 
 predicate UpdateTimeToLiveEnsuresPublicly(input: UpdateTimeToLiveInput , output: Result<UpdateTimeToLiveOutput, Error>)
 // The public method to be called by library consumers
 method UpdateTimeToLive ( input: UpdateTimeToLiveInput )
 returns (output: Result<UpdateTimeToLiveOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdateTimeToLive
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdateTimeToLiveEnsuresPublicly(input, output)
 ensures History.UpdateTimeToLive == old(History.UpdateTimeToLive) + [DafnyCallEvent(input, output)]
 
}
 datatype EnableKinesisStreamingDestinationInput = | EnableKinesisStreamingDestinationInput (
 nameonly TableName: TableName ,
 nameonly StreamArn: StreamArn
 )
 datatype EnableKinesisStreamingDestinationOutput = | EnableKinesisStreamingDestinationOutput (
 nameonly TableName: Option<TableName> ,
 nameonly StreamArn: Option<StreamArn> ,
 nameonly DestinationStatus: Option<DestinationStatus>
 )
 datatype Endpoint = | Endpoint (
 nameonly Address: String ,
 nameonly CachePeriodInMinutes: Long
 )
 type Endpoints = seq<Endpoint>
 type ErrorCount = x: int64 | IsValid_ErrorCount(x) witness *
 predicate method IsValid_ErrorCount(x: int64) {
 ( 0 <= x  )
}
 type ErrorMessage = string
 type ExceptionDescription = string
 type ExceptionName = string
 datatype ExecuteStatementInput = | ExecuteStatementInput (
 nameonly Statement: PartiQLStatement ,
 nameonly Parameters: Option<PreparedStatementParameters> ,
 nameonly ConsistentRead: Option<ConsistentRead> ,
 nameonly NextToken: Option<PartiQLNextToken> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly Limit: Option<PositiveIntegerObject>
 )
 datatype ExecuteStatementOutput = | ExecuteStatementOutput (
 nameonly Items: Option<ItemList> ,
 nameonly NextToken: Option<PartiQLNextToken> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity> ,
 nameonly LastEvaluatedKey: Option<Key>
 )
 datatype ExecuteTransactionInput = | ExecuteTransactionInput (
 nameonly TransactStatements: ParameterizedStatements ,
 nameonly ClientRequestToken: Option<ClientRequestToken> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity>
 )
 datatype ExecuteTransactionOutput = | ExecuteTransactionOutput (
 nameonly Responses: Option<ItemResponseList> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple>
 )
 type ExpectedAttributeMap = map<AttributeName, ExpectedAttributeValue>
 datatype ExpectedAttributeValue = | ExpectedAttributeValue (
 nameonly Value: Option<AttributeValue> ,
 nameonly Exists: Option<BooleanObject> ,
 nameonly ComparisonOperator: Option<ComparisonOperator> ,
 nameonly AttributeValueList: Option<AttributeValueList>
 )
 type ExportArn = x: string | IsValid_ExportArn(x) witness *
 predicate method IsValid_ExportArn(x: string) {
 ( 37 <= |x| <= 1024 )
}
 datatype ExportDescription = | ExportDescription (
 nameonly ExportArn: Option<ExportArn> ,
 nameonly ExportStatus: Option<ExportStatus> ,
 nameonly StartTime: Option<string> ,
 nameonly EndTime: Option<string> ,
 nameonly ExportManifest: Option<ExportManifest> ,
 nameonly TableArn: Option<TableArn> ,
 nameonly TableId: Option<TableId> ,
 nameonly ExportTime: Option<string> ,
 nameonly ClientToken: Option<ClientToken> ,
 nameonly S3Bucket: Option<S3Bucket> ,
 nameonly S3BucketOwner: Option<S3BucketOwner> ,
 nameonly S3Prefix: Option<S3Prefix> ,
 nameonly S3SseAlgorithm: Option<S3SseAlgorithm> ,
 nameonly S3SseKmsKeyId: Option<S3SseKmsKeyId> ,
 nameonly FailureCode: Option<FailureCode> ,
 nameonly FailureMessage: Option<FailureMessage> ,
 nameonly ExportFormat: Option<ExportFormat> ,
 nameonly BilledSizeBytes: Option<BilledSizeBytes> ,
 nameonly ItemCount: Option<ItemCount>
 )
 datatype ExportFormat =
	| DYNAMODB_JSON
	| ION
 type ExportManifest = string
 type ExportNextToken = string
 datatype ExportStatus =
	| IN_PROGRESS
	| COMPLETED
	| FAILED
 type ExportSummaries = seq<ExportSummary>
 datatype ExportSummary = | ExportSummary (
 nameonly ExportArn: Option<ExportArn> ,
 nameonly ExportStatus: Option<ExportStatus>
 )
 datatype ExportTableToPointInTimeInput = | ExportTableToPointInTimeInput (
 nameonly TableArn: TableArn ,
 nameonly ExportTime: Option<string> ,
 nameonly ClientToken: Option<ClientToken> ,
 nameonly S3Bucket: S3Bucket ,
 nameonly S3BucketOwner: Option<S3BucketOwner> ,
 nameonly S3Prefix: Option<S3Prefix> ,
 nameonly S3SseAlgorithm: Option<S3SseAlgorithm> ,
 nameonly S3SseKmsKeyId: Option<S3SseKmsKeyId> ,
 nameonly ExportFormat: Option<ExportFormat>
 )
 datatype ExportTableToPointInTimeOutput = | ExportTableToPointInTimeOutput (
 nameonly ExportDescription: Option<ExportDescription>
 )
 type ExpressionAttributeNameMap = map<ExpressionAttributeNameVariable, AttributeName>
 type ExpressionAttributeNameVariable = string
 type ExpressionAttributeValueMap = map<ExpressionAttributeValueVariable, AttributeValue>
 type ExpressionAttributeValueVariable = string
 type FailureCode = string
 datatype FailureException = | FailureException (
 nameonly ExceptionName: Option<ExceptionName> ,
 nameonly ExceptionDescription: Option<ExceptionDescription>
 )
 type FailureMessage = string
 type FilterConditionMap = map<AttributeName, Condition>
 datatype Get = | Get (
 nameonly Key: Key ,
 nameonly TableName: TableName ,
 nameonly ProjectionExpression: Option<ProjectionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap>
 )
 datatype GetItemInput = | GetItemInput (
 nameonly TableName: TableName ,
 nameonly Key: Key ,
 nameonly AttributesToGet: Option<AttributeNameList> ,
 nameonly ConsistentRead: Option<ConsistentRead> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ProjectionExpression: Option<ProjectionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap>
 )
 datatype GetItemOutput = | GetItemOutput (
 nameonly Item: Option<AttributeMap> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity>
 )
 datatype GlobalSecondaryIndex = | GlobalSecondaryIndex (
 nameonly IndexName: IndexName ,
 nameonly KeySchema: KeySchema ,
 nameonly Projection: Projection ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput>
 )
 datatype GlobalSecondaryIndexAutoScalingUpdate = | GlobalSecondaryIndexAutoScalingUpdate (
 nameonly IndexName: Option<IndexName> ,
 nameonly ProvisionedWriteCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate>
 )
 type GlobalSecondaryIndexAutoScalingUpdateList = x: seq<GlobalSecondaryIndexAutoScalingUpdate> | IsValid_GlobalSecondaryIndexAutoScalingUpdateList(x) witness *
 predicate method IsValid_GlobalSecondaryIndexAutoScalingUpdateList(x: seq<GlobalSecondaryIndexAutoScalingUpdate>) {
 ( 1 <= |x|  )
}
 datatype GlobalSecondaryIndexDescription = | GlobalSecondaryIndexDescription (
 nameonly IndexName: Option<IndexName> ,
 nameonly KeySchema: Option<KeySchema> ,
 nameonly Projection: Option<Projection> ,
 nameonly IndexStatus: Option<IndexStatus> ,
 nameonly Backfilling: Option<Backfilling> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughputDescription> ,
 nameonly IndexSizeBytes: Option<Long> ,
 nameonly ItemCount: Option<Long> ,
 nameonly IndexArn: Option<String>
 )
 type GlobalSecondaryIndexDescriptionList = seq<GlobalSecondaryIndexDescription>
 type GlobalSecondaryIndexes = seq<GlobalSecondaryIndexInfo>
 datatype GlobalSecondaryIndexInfo = | GlobalSecondaryIndexInfo (
 nameonly IndexName: Option<IndexName> ,
 nameonly KeySchema: Option<KeySchema> ,
 nameonly Projection: Option<Projection> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput>
 )
 type GlobalSecondaryIndexList = seq<GlobalSecondaryIndex>
 datatype GlobalSecondaryIndexUpdate = | GlobalSecondaryIndexUpdate (
 nameonly Update: Option<UpdateGlobalSecondaryIndexAction> ,
 nameonly Create: Option<CreateGlobalSecondaryIndexAction> ,
 nameonly Delete: Option<DeleteGlobalSecondaryIndexAction>
 )
 type GlobalSecondaryIndexUpdateList = seq<GlobalSecondaryIndexUpdate>
 datatype GlobalTable = | GlobalTable (
 nameonly GlobalTableName: Option<TableName> ,
 nameonly ReplicationGroup: Option<ReplicaList>
 )
 type GlobalTableArnString = string
 datatype GlobalTableDescription = | GlobalTableDescription (
 nameonly ReplicationGroup: Option<ReplicaDescriptionList> ,
 nameonly GlobalTableArn: Option<GlobalTableArnString> ,
 nameonly CreationDateTime: Option<string> ,
 nameonly GlobalTableStatus: Option<GlobalTableStatus> ,
 nameonly GlobalTableName: Option<TableName>
 )
 datatype GlobalTableGlobalSecondaryIndexSettingsUpdate = | GlobalTableGlobalSecondaryIndexSettingsUpdate (
 nameonly IndexName: IndexName ,
 nameonly ProvisionedWriteCapacityUnits: Option<PositiveLongObject> ,
 nameonly ProvisionedWriteCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate>
 )
 type GlobalTableGlobalSecondaryIndexSettingsUpdateList = x: seq<GlobalTableGlobalSecondaryIndexSettingsUpdate> | IsValid_GlobalTableGlobalSecondaryIndexSettingsUpdateList(x) witness *
 predicate method IsValid_GlobalTableGlobalSecondaryIndexSettingsUpdateList(x: seq<GlobalTableGlobalSecondaryIndexSettingsUpdate>) {
 ( 1 <= |x| <= 20 )
}
 type GlobalTableList = seq<GlobalTable>
 datatype GlobalTableStatus =
	| CREATING
	| ACTIVE
	| DELETING
	| UPDATING
 type ImportArn = x: string | IsValid_ImportArn(x) witness *
 predicate method IsValid_ImportArn(x: string) {
 ( 37 <= |x| <= 1024 )
}
 type ImportedItemCount = x: int64 | IsValid_ImportedItemCount(x) witness *
 predicate method IsValid_ImportedItemCount(x: int64) {
 ( 0 <= x  )
}
 type ImportNextToken = x: string | IsValid_ImportNextToken(x) witness *
 predicate method IsValid_ImportNextToken(x: string) {
 ( 112 <= |x| <= 1024 )
}
 datatype ImportStatus =
	| IN_PROGRESS
	| COMPLETED
	| CANCELLING
	| CANCELLED
	| FAILED
 datatype ImportSummary = | ImportSummary (
 nameonly ImportArn: Option<ImportArn> ,
 nameonly ImportStatus: Option<ImportStatus> ,
 nameonly TableArn: Option<TableArn> ,
 nameonly S3BucketSource: Option<S3BucketSource> ,
 nameonly CloudWatchLogGroupArn: Option<CloudWatchLogGroupArn> ,
 nameonly InputFormat: Option<InputFormat> ,
 nameonly StartTime: Option<string> ,
 nameonly EndTime: Option<string>
 )
 type ImportSummaryList = seq<ImportSummary>
 datatype ImportTableDescription = | ImportTableDescription (
 nameonly ImportArn: Option<ImportArn> ,
 nameonly ImportStatus: Option<ImportStatus> ,
 nameonly TableArn: Option<TableArn> ,
 nameonly TableId: Option<TableId> ,
 nameonly ClientToken: Option<ClientToken> ,
 nameonly S3BucketSource: Option<S3BucketSource> ,
 nameonly ErrorCount: Option<ErrorCount> ,
 nameonly CloudWatchLogGroupArn: Option<CloudWatchLogGroupArn> ,
 nameonly InputFormat: Option<InputFormat> ,
 nameonly InputFormatOptions: Option<InputFormatOptions> ,
 nameonly InputCompressionType: Option<InputCompressionType> ,
 nameonly TableCreationParameters: Option<TableCreationParameters> ,
 nameonly StartTime: Option<string> ,
 nameonly EndTime: Option<string> ,
 nameonly ProcessedSizeBytes: Option<Long> ,
 nameonly ProcessedItemCount: Option<ProcessedItemCount> ,
 nameonly ImportedItemCount: Option<ImportedItemCount> ,
 nameonly FailureCode: Option<FailureCode> ,
 nameonly FailureMessage: Option<FailureMessage>
 )
 datatype ImportTableInput = | ImportTableInput (
 nameonly ClientToken: Option<ClientToken> ,
 nameonly S3BucketSource: S3BucketSource ,
 nameonly InputFormat: InputFormat ,
 nameonly InputFormatOptions: Option<InputFormatOptions> ,
 nameonly InputCompressionType: Option<InputCompressionType> ,
 nameonly TableCreationParameters: TableCreationParameters
 )
 datatype ImportTableOutput = | ImportTableOutput (
 nameonly ImportTableDescription: ImportTableDescription
 )
 type IndexName = x: string | IsValid_IndexName(x) witness *
 predicate method IsValid_IndexName(x: string) {
 ( 3 <= |x| <= 255 )
}
 datatype IndexStatus =
	| CREATING
	| UPDATING
	| DELETING
	| ACTIVE
 datatype InputCompressionType =
	| GZIP
	| ZSTD
	| NONE
 datatype InputFormat =
	| DYNAMODB_JSON
	| ION
	| CSV
 datatype InputFormatOptions = | InputFormatOptions (
 nameonly Csv: Option<CsvOptions>
 )
 type Integer = int32
 type IntegerObject = int32
 type ItemCollectionKeyAttributeMap = map<AttributeName, AttributeValue>
 datatype ItemCollectionMetrics = | ItemCollectionMetrics (
 nameonly ItemCollectionKey: Option<ItemCollectionKeyAttributeMap> ,
 nameonly SizeEstimateRangeGB: Option<ItemCollectionSizeEstimateRange>
 )
 type ItemCollectionMetricsMultiple = seq<ItemCollectionMetrics>
 type ItemCollectionMetricsPerTable = map<TableName, ItemCollectionMetricsMultiple>
 type ItemCollectionSizeEstimateBound = int32
 type ItemCollectionSizeEstimateRange = seq<ItemCollectionSizeEstimateBound>
 type ItemCount = x: int64 | IsValid_ItemCount(x) witness *
 predicate method IsValid_ItemCount(x: int64) {
 ( 0 <= x  )
}
 type ItemList = seq<AttributeMap>
 datatype ItemResponse = | ItemResponse (
 nameonly Item: Option<AttributeMap>
 )
 type ItemResponseList = x: seq<ItemResponse> | IsValid_ItemResponseList(x) witness *
 predicate method IsValid_ItemResponseList(x: seq<ItemResponse>) {
 ( 1 <= |x| <= 25 )
}
 type Key = map<AttributeName, AttributeValue>
 type KeyConditions = map<AttributeName, Condition>
 type KeyExpression = string
 type KeyList = x: seq<Key> | IsValid_KeyList(x) witness *
 predicate method IsValid_KeyList(x: seq<Key>) {
 ( 1 <= |x| <= 100 )
}
 datatype KeysAndAttributes = | KeysAndAttributes (
 nameonly Keys: KeyList ,
 nameonly AttributesToGet: Option<AttributeNameList> ,
 nameonly ConsistentRead: Option<ConsistentRead> ,
 nameonly ProjectionExpression: Option<ProjectionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap>
 )
 type KeySchema = x: seq<KeySchemaElement> | IsValid_KeySchema(x) witness *
 predicate method IsValid_KeySchema(x: seq<KeySchemaElement>) {
 ( 1 <= |x| <= 2 )
}
 type KeySchemaAttributeName = x: string | IsValid_KeySchemaAttributeName(x) witness *
 predicate method IsValid_KeySchemaAttributeName(x: string) {
 ( 1 <= |x| <= 255 )
}
 datatype KeySchemaElement = | KeySchemaElement (
 nameonly AttributeName: KeySchemaAttributeName ,
 nameonly KeyType: KeyType
 )
 datatype KeyType =
	| HASH
	| RANGE
 datatype KinesisDataStreamDestination = | KinesisDataStreamDestination (
 nameonly StreamArn: Option<StreamArn> ,
 nameonly DestinationStatus: Option<DestinationStatus> ,
 nameonly DestinationStatusDescription: Option<String>
 )
 type KinesisDataStreamDestinations = seq<KinesisDataStreamDestination>
 datatype KinesisStreamingDestinationInput = | KinesisStreamingDestinationInput (
 nameonly TableName: TableName ,
 nameonly StreamArn: StreamArn
 )
 datatype KinesisStreamingDestinationOutput = | KinesisStreamingDestinationOutput (
 nameonly TableName: Option<TableName> ,
 nameonly StreamArn: Option<StreamArn> ,
 nameonly DestinationStatus: Option<DestinationStatus>
 )
 type KMSMasterKeyArn = string
 type KMSMasterKeyId = string
 type ListAttributeValue = seq<AttributeValue>
 datatype ListBackupsInput = | ListBackupsInput (
 nameonly TableName: Option<TableName> ,
 nameonly Limit: Option<BackupsInputLimit> ,
 nameonly TimeRangeLowerBound: Option<string> ,
 nameonly TimeRangeUpperBound: Option<string> ,
 nameonly ExclusiveStartBackupArn: Option<BackupArn> ,
 nameonly BackupType: Option<BackupTypeFilter>
 )
 datatype ListBackupsOutput = | ListBackupsOutput (
 nameonly BackupSummaries: Option<BackupSummaries> ,
 nameonly LastEvaluatedBackupArn: Option<BackupArn>
 )
 datatype ListContributorInsightsInput = | ListContributorInsightsInput (
 nameonly TableName: Option<TableName> ,
 nameonly NextToken: Option<NextTokenString> ,
 nameonly MaxResults: Option<ListContributorInsightsLimit>
 )
 type ListContributorInsightsLimit = x: int32 | IsValid_ListContributorInsightsLimit(x) witness *
 predicate method IsValid_ListContributorInsightsLimit(x: int32) {
 (  x <= 100 )
}
 datatype ListContributorInsightsOutput = | ListContributorInsightsOutput (
 nameonly ContributorInsightsSummaries: Option<ContributorInsightsSummaries> ,
 nameonly NextToken: Option<NextTokenString>
 )
 datatype ListExportsInput = | ListExportsInput (
 nameonly TableArn: Option<TableArn> ,
 nameonly MaxResults: Option<ListExportsMaxLimit> ,
 nameonly NextToken: Option<ExportNextToken>
 )
 type ListExportsMaxLimit = x: int32 | IsValid_ListExportsMaxLimit(x) witness *
 predicate method IsValid_ListExportsMaxLimit(x: int32) {
 ( 1 <= x <= 25 )
}
 datatype ListExportsOutput = | ListExportsOutput (
 nameonly ExportSummaries: Option<ExportSummaries> ,
 nameonly NextToken: Option<ExportNextToken>
 )
 datatype ListGlobalTablesInput = | ListGlobalTablesInput (
 nameonly ExclusiveStartGlobalTableName: Option<TableName> ,
 nameonly Limit: Option<PositiveIntegerObject> ,
 nameonly RegionName: Option<RegionName>
 )
 datatype ListGlobalTablesOutput = | ListGlobalTablesOutput (
 nameonly GlobalTables: Option<GlobalTableList> ,
 nameonly LastEvaluatedGlobalTableName: Option<TableName>
 )
 datatype ListImportsInput = | ListImportsInput (
 nameonly TableArn: Option<TableArn> ,
 nameonly PageSize: Option<ListImportsMaxLimit> ,
 nameonly NextToken: Option<ImportNextToken>
 )
 type ListImportsMaxLimit = x: int32 | IsValid_ListImportsMaxLimit(x) witness *
 predicate method IsValid_ListImportsMaxLimit(x: int32) {
 ( 1 <= x <= 25 )
}
 datatype ListImportsOutput = | ListImportsOutput (
 nameonly ImportSummaryList: Option<ImportSummaryList> ,
 nameonly NextToken: Option<ImportNextToken>
 )
 datatype ListTablesInput = | ListTablesInput (
 nameonly ExclusiveStartTableName: Option<TableName> ,
 nameonly Limit: Option<ListTablesInputLimit>
 )
 type ListTablesInputLimit = x: int32 | IsValid_ListTablesInputLimit(x) witness *
 predicate method IsValid_ListTablesInputLimit(x: int32) {
 ( 1 <= x <= 100 )
}
 datatype ListTablesOutput = | ListTablesOutput (
 nameonly TableNames: Option<TableNameList> ,
 nameonly LastEvaluatedTableName: Option<TableName>
 )
 datatype ListTagsOfResourceInput = | ListTagsOfResourceInput (
 nameonly ResourceArn: ResourceArnString ,
 nameonly NextToken: Option<NextTokenString>
 )
 datatype ListTagsOfResourceOutput = | ListTagsOfResourceOutput (
 nameonly Tags: Option<TagList> ,
 nameonly NextToken: Option<NextTokenString>
 )
 datatype LocalSecondaryIndex = | LocalSecondaryIndex (
 nameonly IndexName: IndexName ,
 nameonly KeySchema: KeySchema ,
 nameonly Projection: Projection
 )
 datatype LocalSecondaryIndexDescription = | LocalSecondaryIndexDescription (
 nameonly IndexName: Option<IndexName> ,
 nameonly KeySchema: Option<KeySchema> ,
 nameonly Projection: Option<Projection> ,
 nameonly IndexSizeBytes: Option<Long> ,
 nameonly ItemCount: Option<Long> ,
 nameonly IndexArn: Option<String>
 )
 type LocalSecondaryIndexDescriptionList = seq<LocalSecondaryIndexDescription>
 type LocalSecondaryIndexes = seq<LocalSecondaryIndexInfo>
 datatype LocalSecondaryIndexInfo = | LocalSecondaryIndexInfo (
 nameonly IndexName: Option<IndexName> ,
 nameonly KeySchema: Option<KeySchema> ,
 nameonly Projection: Option<Projection>
 )
 type LocalSecondaryIndexList = seq<LocalSecondaryIndex>
 type Long = int64
 type MapAttributeValue = map<AttributeName, AttributeValue>
 type NextTokenString = string
 type NonKeyAttributeName = x: string | IsValid_NonKeyAttributeName(x) witness *
 predicate method IsValid_NonKeyAttributeName(x: string) {
 ( 1 <= |x| <= 255 )
}
 type NonKeyAttributeNameList = x: seq<NonKeyAttributeName> | IsValid_NonKeyAttributeNameList(x) witness *
 predicate method IsValid_NonKeyAttributeNameList(x: seq<NonKeyAttributeName>) {
 ( 1 <= |x| <= 20 )
}
 type NonNegativeLongObject = x: int64 | IsValid_NonNegativeLongObject(x) witness *
 predicate method IsValid_NonNegativeLongObject(x: int64) {
 ( 0 <= x  )
}
 type NullAttributeValue = bool
 type NumberAttributeValue = string
 type NumberSetAttributeValue = seq<NumberAttributeValue>
 datatype ParameterizedStatement = | ParameterizedStatement (
 nameonly Statement: PartiQLStatement ,
 nameonly Parameters: Option<PreparedStatementParameters>
 )
 type ParameterizedStatements = x: seq<ParameterizedStatement> | IsValid_ParameterizedStatements(x) witness *
 predicate method IsValid_ParameterizedStatements(x: seq<ParameterizedStatement>) {
 ( 1 <= |x| <= 25 )
}
 type PartiQLBatchRequest = x: seq<BatchStatementRequest> | IsValid_PartiQLBatchRequest(x) witness *
 predicate method IsValid_PartiQLBatchRequest(x: seq<BatchStatementRequest>) {
 ( 1 <= |x| <= 25 )
}
 type PartiQLBatchResponse = seq<BatchStatementResponse>
 type PartiQLNextToken = x: string | IsValid_PartiQLNextToken(x) witness *
 predicate method IsValid_PartiQLNextToken(x: string) {
 ( 1 <= |x| <= 32768 )
}
 type PartiQLStatement = x: string | IsValid_PartiQLStatement(x) witness *
 predicate method IsValid_PartiQLStatement(x: string) {
 ( 1 <= |x| <= 8192 )
}
 datatype PointInTimeRecoveryDescription = | PointInTimeRecoveryDescription (
 nameonly PointInTimeRecoveryStatus: Option<PointInTimeRecoveryStatus> ,
 nameonly EarliestRestorableDateTime: Option<string> ,
 nameonly LatestRestorableDateTime: Option<string>
 )
 datatype PointInTimeRecoverySpecification = | PointInTimeRecoverySpecification (
 nameonly PointInTimeRecoveryEnabled: BooleanObject
 )
 datatype PointInTimeRecoveryStatus =
	| ENABLED
	| DISABLED
 type PositiveIntegerObject = x: int32 | IsValid_PositiveIntegerObject(x) witness *
 predicate method IsValid_PositiveIntegerObject(x: int32) {
 ( 1 <= x  )
}
 type PositiveLongObject = x: int64 | IsValid_PositiveLongObject(x) witness *
 predicate method IsValid_PositiveLongObject(x: int64) {
 ( 1 <= x  )
}
 type PreparedStatementParameters = x: seq<AttributeValue> | IsValid_PreparedStatementParameters(x) witness *
 predicate method IsValid_PreparedStatementParameters(x: seq<AttributeValue>) {
 ( 1 <= |x|  )
}
 type ProcessedItemCount = x: int64 | IsValid_ProcessedItemCount(x) witness *
 predicate method IsValid_ProcessedItemCount(x: int64) {
 ( 0 <= x  )
}
 datatype Projection = | Projection (
 nameonly ProjectionType: Option<ProjectionType> ,
 nameonly NonKeyAttributes: Option<NonKeyAttributeNameList>
 )
 type ProjectionExpression = string
 datatype ProjectionType =
	| ALL
	| KEYS_ONLY
	| INCLUDE
 datatype ProvisionedThroughput = | ProvisionedThroughput (
 nameonly ReadCapacityUnits: PositiveLongObject ,
 nameonly WriteCapacityUnits: PositiveLongObject
 )
 datatype ProvisionedThroughputDescription = | ProvisionedThroughputDescription (
 nameonly LastIncreaseDateTime: Option<string> ,
 nameonly LastDecreaseDateTime: Option<string> ,
 nameonly NumberOfDecreasesToday: Option<PositiveLongObject> ,
 nameonly ReadCapacityUnits: Option<NonNegativeLongObject> ,
 nameonly WriteCapacityUnits: Option<NonNegativeLongObject>
 )
 datatype ProvisionedThroughputOverride = | ProvisionedThroughputOverride (
 nameonly ReadCapacityUnits: Option<PositiveLongObject>
 )
 datatype Put = | Put (
 nameonly Item: PutItemInputAttributeMap ,
 nameonly TableName: TableName ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> ,
 nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure>
 )
 datatype PutItemInput = | PutItemInput (
 nameonly TableName: TableName ,
 nameonly Item: PutItemInputAttributeMap ,
 nameonly Expected: Option<ExpectedAttributeMap> ,
 nameonly ReturnValues: Option<ReturnValue> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> ,
 nameonly ConditionalOperator: Option<ConditionalOperator> ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap>
 )
 type PutItemInputAttributeMap = map<AttributeName, AttributeValue>
 datatype PutItemOutput = | PutItemOutput (
 nameonly Attributes: Option<AttributeMap> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity> ,
 nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics>
 )
 datatype PutRequest = | PutRequest (
 nameonly Item: PutItemInputAttributeMap
 )
 datatype QueryInput = | QueryInput (
 nameonly TableName: TableName ,
 nameonly IndexName: Option<IndexName> ,
 nameonly Select: Option<Select> ,
 nameonly AttributesToGet: Option<AttributeNameList> ,
 nameonly Limit: Option<PositiveIntegerObject> ,
 nameonly ConsistentRead: Option<ConsistentRead> ,
 nameonly KeyConditions: Option<KeyConditions> ,
 nameonly QueryFilter: Option<FilterConditionMap> ,
 nameonly ConditionalOperator: Option<ConditionalOperator> ,
 nameonly ScanIndexForward: Option<BooleanObject> ,
 nameonly ExclusiveStartKey: Option<Key> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ProjectionExpression: Option<ProjectionExpression> ,
 nameonly FilterExpression: Option<ConditionExpression> ,
 nameonly KeyConditionExpression: Option<KeyExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap>
 )
 datatype QueryOutput = | QueryOutput (
 nameonly Items: Option<ItemList> ,
 nameonly Count: Option<Integer> ,
 nameonly ScannedCount: Option<Integer> ,
 nameonly LastEvaluatedKey: Option<Key> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity>
 )
 type RegionName = string
 datatype Replica = | Replica (
 nameonly RegionName: Option<RegionName>
 )
 datatype ReplicaAutoScalingDescription = | ReplicaAutoScalingDescription (
 nameonly RegionName: Option<RegionName> ,
 nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexAutoScalingDescriptionList> ,
 nameonly ReplicaProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ReplicaProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ReplicaStatus: Option<ReplicaStatus>
 )
 type ReplicaAutoScalingDescriptionList = seq<ReplicaAutoScalingDescription>
 datatype ReplicaAutoScalingUpdate = | ReplicaAutoScalingUpdate (
 nameonly RegionName: RegionName ,
 nameonly ReplicaGlobalSecondaryIndexUpdates: Option<ReplicaGlobalSecondaryIndexAutoScalingUpdateList> ,
 nameonly ReplicaProvisionedReadCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate>
 )
 type ReplicaAutoScalingUpdateList = x: seq<ReplicaAutoScalingUpdate> | IsValid_ReplicaAutoScalingUpdateList(x) witness *
 predicate method IsValid_ReplicaAutoScalingUpdateList(x: seq<ReplicaAutoScalingUpdate>) {
 ( 1 <= |x|  )
}
 datatype ReplicaDescription = | ReplicaDescription (
 nameonly RegionName: Option<RegionName> ,
 nameonly ReplicaStatus: Option<ReplicaStatus> ,
 nameonly ReplicaStatusDescription: Option<ReplicaStatusDescription> ,
 nameonly ReplicaStatusPercentProgress: Option<ReplicaStatusPercentProgress> ,
 nameonly KMSMasterKeyId: Option<KMSMasterKeyId> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> ,
 nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexDescriptionList> ,
 nameonly ReplicaInaccessibleDateTime: Option<string> ,
 nameonly ReplicaTableClassSummary: Option<TableClassSummary>
 )
 type ReplicaDescriptionList = seq<ReplicaDescription>
 datatype ReplicaGlobalSecondaryIndex = | ReplicaGlobalSecondaryIndex (
 nameonly IndexName: IndexName ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride>
 )
 datatype ReplicaGlobalSecondaryIndexAutoScalingDescription = | ReplicaGlobalSecondaryIndexAutoScalingDescription (
 nameonly IndexName: Option<IndexName> ,
 nameonly IndexStatus: Option<IndexStatus> ,
 nameonly ProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription>
 )
 type ReplicaGlobalSecondaryIndexAutoScalingDescriptionList = seq<ReplicaGlobalSecondaryIndexAutoScalingDescription>
 datatype ReplicaGlobalSecondaryIndexAutoScalingUpdate = | ReplicaGlobalSecondaryIndexAutoScalingUpdate (
 nameonly IndexName: Option<IndexName> ,
 nameonly ProvisionedReadCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate>
 )
 type ReplicaGlobalSecondaryIndexAutoScalingUpdateList = seq<ReplicaGlobalSecondaryIndexAutoScalingUpdate>
 datatype ReplicaGlobalSecondaryIndexDescription = | ReplicaGlobalSecondaryIndexDescription (
 nameonly IndexName: Option<IndexName> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride>
 )
 type ReplicaGlobalSecondaryIndexDescriptionList = seq<ReplicaGlobalSecondaryIndexDescription>
 type ReplicaGlobalSecondaryIndexList = x: seq<ReplicaGlobalSecondaryIndex> | IsValid_ReplicaGlobalSecondaryIndexList(x) witness *
 predicate method IsValid_ReplicaGlobalSecondaryIndexList(x: seq<ReplicaGlobalSecondaryIndex>) {
 ( 1 <= |x|  )
}
 datatype ReplicaGlobalSecondaryIndexSettingsDescription = | ReplicaGlobalSecondaryIndexSettingsDescription (
 nameonly IndexName: IndexName ,
 nameonly IndexStatus: Option<IndexStatus> ,
 nameonly ProvisionedReadCapacityUnits: Option<PositiveLongObject> ,
 nameonly ProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ProvisionedWriteCapacityUnits: Option<PositiveLongObject> ,
 nameonly ProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription>
 )
 type ReplicaGlobalSecondaryIndexSettingsDescriptionList = seq<ReplicaGlobalSecondaryIndexSettingsDescription>
 datatype ReplicaGlobalSecondaryIndexSettingsUpdate = | ReplicaGlobalSecondaryIndexSettingsUpdate (
 nameonly IndexName: IndexName ,
 nameonly ProvisionedReadCapacityUnits: Option<PositiveLongObject> ,
 nameonly ProvisionedReadCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate>
 )
 type ReplicaGlobalSecondaryIndexSettingsUpdateList = x: seq<ReplicaGlobalSecondaryIndexSettingsUpdate> | IsValid_ReplicaGlobalSecondaryIndexSettingsUpdateList(x) witness *
 predicate method IsValid_ReplicaGlobalSecondaryIndexSettingsUpdateList(x: seq<ReplicaGlobalSecondaryIndexSettingsUpdate>) {
 ( 1 <= |x| <= 20 )
}
 type ReplicaList = seq<Replica>
 datatype ReplicaSettingsDescription = | ReplicaSettingsDescription (
 nameonly RegionName: RegionName ,
 nameonly ReplicaStatus: Option<ReplicaStatus> ,
 nameonly ReplicaBillingModeSummary: Option<BillingModeSummary> ,
 nameonly ReplicaProvisionedReadCapacityUnits: Option<NonNegativeLongObject> ,
 nameonly ReplicaProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ReplicaProvisionedWriteCapacityUnits: Option<NonNegativeLongObject> ,
 nameonly ReplicaProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> ,
 nameonly ReplicaGlobalSecondaryIndexSettings: Option<ReplicaGlobalSecondaryIndexSettingsDescriptionList> ,
 nameonly ReplicaTableClassSummary: Option<TableClassSummary>
 )
 type ReplicaSettingsDescriptionList = seq<ReplicaSettingsDescription>
 datatype ReplicaSettingsUpdate = | ReplicaSettingsUpdate (
 nameonly RegionName: RegionName ,
 nameonly ReplicaProvisionedReadCapacityUnits: Option<PositiveLongObject> ,
 nameonly ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> ,
 nameonly ReplicaGlobalSecondaryIndexSettingsUpdate: Option<ReplicaGlobalSecondaryIndexSettingsUpdateList> ,
 nameonly ReplicaTableClass: Option<TableClass>
 )
 type ReplicaSettingsUpdateList = x: seq<ReplicaSettingsUpdate> | IsValid_ReplicaSettingsUpdateList(x) witness *
 predicate method IsValid_ReplicaSettingsUpdateList(x: seq<ReplicaSettingsUpdate>) {
 ( 1 <= |x| <= 50 )
}
 datatype ReplicaStatus =
	| CREATING
	| CREATION_FAILED
	| UPDATING
	| DELETING
	| ACTIVE
	| REGION_DISABLED
	| INACCESSIBLE_ENCRYPTION_CREDENTIALS
 type ReplicaStatusDescription = string
 type ReplicaStatusPercentProgress = string
 datatype ReplicationGroupUpdate = | ReplicationGroupUpdate (
 nameonly Create: Option<CreateReplicationGroupMemberAction> ,
 nameonly Update: Option<UpdateReplicationGroupMemberAction> ,
 nameonly Delete: Option<DeleteReplicationGroupMemberAction>
 )
 type ReplicationGroupUpdateList = x: seq<ReplicationGroupUpdate> | IsValid_ReplicationGroupUpdateList(x) witness *
 predicate method IsValid_ReplicationGroupUpdateList(x: seq<ReplicationGroupUpdate>) {
 ( 1 <= |x|  )
}
 datatype ReplicaUpdate = | ReplicaUpdate (
 nameonly Create: Option<CreateReplicaAction> ,
 nameonly Delete: Option<DeleteReplicaAction>
 )
 type ReplicaUpdateList = seq<ReplicaUpdate>
 type ResourceArnString = x: string | IsValid_ResourceArnString(x) witness *
 predicate method IsValid_ResourceArnString(x: string) {
 ( 1 <= |x| <= 1283 )
}
 type RestoreInProgress = bool
 datatype RestoreSummary = | RestoreSummary (
 nameonly SourceBackupArn: Option<BackupArn> ,
 nameonly SourceTableArn: Option<TableArn> ,
 nameonly RestoreDateTime: string ,
 nameonly RestoreInProgress: RestoreInProgress
 )
 datatype RestoreTableFromBackupInput = | RestoreTableFromBackupInput (
 nameonly TargetTableName: TableName ,
 nameonly BackupArn: BackupArn ,
 nameonly BillingModeOverride: Option<BillingMode> ,
 nameonly GlobalSecondaryIndexOverride: Option<GlobalSecondaryIndexList> ,
 nameonly LocalSecondaryIndexOverride: Option<LocalSecondaryIndexList> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughput> ,
 nameonly SSESpecificationOverride: Option<SSESpecification>
 )
 datatype RestoreTableFromBackupOutput = | RestoreTableFromBackupOutput (
 nameonly TableDescription: Option<TableDescription>
 )
 datatype RestoreTableToPointInTimeInput = | RestoreTableToPointInTimeInput (
 nameonly SourceTableArn: Option<TableArn> ,
 nameonly SourceTableName: Option<TableName> ,
 nameonly TargetTableName: TableName ,
 nameonly UseLatestRestorableTime: Option<BooleanObject> ,
 nameonly RestoreDateTime: Option<string> ,
 nameonly BillingModeOverride: Option<BillingMode> ,
 nameonly GlobalSecondaryIndexOverride: Option<GlobalSecondaryIndexList> ,
 nameonly LocalSecondaryIndexOverride: Option<LocalSecondaryIndexList> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughput> ,
 nameonly SSESpecificationOverride: Option<SSESpecification>
 )
 datatype RestoreTableToPointInTimeOutput = | RestoreTableToPointInTimeOutput (
 nameonly TableDescription: Option<TableDescription>
 )
 datatype ReturnConsumedCapacity =
	| INDEXES
	| TOTAL
	| NONE
 datatype ReturnItemCollectionMetrics =
	| SIZE
	| NONE
 datatype ReturnValue =
	| NONE
	| ALL_OLD
	| UPDATED_OLD
	| ALL_NEW
	| UPDATED_NEW
 datatype ReturnValuesOnConditionCheckFailure =
	| ALL_OLD
	| NONE
 type S3Bucket = x: string | IsValid_S3Bucket(x) witness *
 predicate method IsValid_S3Bucket(x: string) {
 ( 0 <= |x| <= 255 )
}
 type S3BucketOwner = string
 datatype S3BucketSource = | S3BucketSource (
 nameonly S3BucketOwner: Option<S3BucketOwner> ,
 nameonly S3Bucket: S3Bucket ,
 nameonly S3KeyPrefix: Option<S3Prefix>
 )
 type S3Prefix = x: string | IsValid_S3Prefix(x) witness *
 predicate method IsValid_S3Prefix(x: string) {
 ( 0 <= |x| <= 1024 )
}
 datatype S3SseAlgorithm =
	| AES256
	| KMS
 type S3SseKmsKeyId = x: string | IsValid_S3SseKmsKeyId(x) witness *
 predicate method IsValid_S3SseKmsKeyId(x: string) {
 ( 1 <= |x| <= 2048 )
}
 datatype ScalarAttributeType =
	| S
	| N
	| B
 datatype ScanInput = | ScanInput (
 nameonly TableName: TableName ,
 nameonly IndexName: Option<IndexName> ,
 nameonly AttributesToGet: Option<AttributeNameList> ,
 nameonly Limit: Option<PositiveIntegerObject> ,
 nameonly Select: Option<Select> ,
 nameonly ScanFilter: Option<FilterConditionMap> ,
 nameonly ConditionalOperator: Option<ConditionalOperator> ,
 nameonly ExclusiveStartKey: Option<Key> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly TotalSegments: Option<ScanTotalSegments> ,
 nameonly Segment: Option<ScanSegment> ,
 nameonly ProjectionExpression: Option<ProjectionExpression> ,
 nameonly FilterExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> ,
 nameonly ConsistentRead: Option<ConsistentRead>
 )
 datatype ScanOutput = | ScanOutput (
 nameonly Items: Option<ItemList> ,
 nameonly Count: Option<Integer> ,
 nameonly ScannedCount: Option<Integer> ,
 nameonly LastEvaluatedKey: Option<Key> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity>
 )
 type ScanSegment = x: int32 | IsValid_ScanSegment(x) witness *
 predicate method IsValid_ScanSegment(x: int32) {
 ( 0 <= x <= 999999 )
}
 type ScanTotalSegments = x: int32 | IsValid_ScanTotalSegments(x) witness *
 predicate method IsValid_ScanTotalSegments(x: int32) {
 ( 1 <= x <= 1000000 )
}
 type SecondaryIndexesCapacityMap = map<IndexName, Capacity>
 datatype Select =
	| ALL_ATTRIBUTES
	| ALL_PROJECTED_ATTRIBUTES
	| SPECIFIC_ATTRIBUTES
	| COUNT
 datatype SourceTableDetails = | SourceTableDetails (
 nameonly TableName: TableName ,
 nameonly TableId: TableId ,
 nameonly TableArn: Option<TableArn> ,
 nameonly TableSizeBytes: Option<Long> ,
 nameonly KeySchema: KeySchema ,
 nameonly TableCreationDateTime: string ,
 nameonly ProvisionedThroughput: ProvisionedThroughput ,
 nameonly ItemCount: Option<ItemCount> ,
 nameonly BillingMode: Option<BillingMode>
 )
 datatype SourceTableFeatureDetails = | SourceTableFeatureDetails (
 nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexes> ,
 nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexes> ,
 nameonly StreamDescription: Option<StreamSpecification> ,
 nameonly TimeToLiveDescription: Option<TimeToLiveDescription> ,
 nameonly SSEDescription: Option<SSEDescription>
 )
 datatype SSEDescription = | SSEDescription (
 nameonly Status: Option<SSEStatus> ,
 nameonly SSEType: Option<SSEType> ,
 nameonly KMSMasterKeyArn: Option<KMSMasterKeyArn> ,
 nameonly InaccessibleEncryptionDateTime: Option<string>
 )
 type SSEEnabled = bool
 datatype SSESpecification = | SSESpecification (
 nameonly Enabled: Option<SSEEnabled> ,
 nameonly SSEType: Option<SSEType> ,
 nameonly KMSMasterKeyId: Option<KMSMasterKeyId>
 )
 datatype SSEStatus =
	| ENABLING
	| ENABLED
	| DISABLING
	| DISABLED
	| UPDATING
 datatype SSEType =
	| AES256
	| KMS
 type StreamArn = x: string | IsValid_StreamArn(x) witness *
 predicate method IsValid_StreamArn(x: string) {
 ( 37 <= |x| <= 1024 )
}
 type StreamEnabled = bool
 datatype StreamSpecification = | StreamSpecification (
 nameonly StreamEnabled: StreamEnabled ,
 nameonly StreamViewType: Option<StreamViewType>
 )
 datatype StreamViewType =
	| NEW_IMAGE
	| OLD_IMAGE
	| NEW_AND_OLD_IMAGES
	| KEYS_ONLY
 type String = string
 type StringAttributeValue = string
 type StringSetAttributeValue = seq<StringAttributeValue>
 type TableArn = string
 datatype TableAutoScalingDescription = | TableAutoScalingDescription (
 nameonly TableName: Option<TableName> ,
 nameonly TableStatus: Option<TableStatus> ,
 nameonly Replicas: Option<ReplicaAutoScalingDescriptionList>
 )
 datatype TableClass =
	| STANDARD
	| STANDARD_INFREQUENT_ACCESS
 datatype TableClassSummary = | TableClassSummary (
 nameonly TableClass: Option<TableClass> ,
 nameonly LastUpdateDateTime: Option<string>
 )
 datatype TableCreationParameters = | TableCreationParameters (
 nameonly TableName: TableName ,
 nameonly AttributeDefinitions: AttributeDefinitions ,
 nameonly KeySchema: KeySchema ,
 nameonly BillingMode: Option<BillingMode> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput> ,
 nameonly SSESpecification: Option<SSESpecification> ,
 nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexList>
 )
 datatype TableDescription = | TableDescription (
 nameonly AttributeDefinitions: Option<AttributeDefinitions> ,
 nameonly TableName: Option<TableName> ,
 nameonly KeySchema: Option<KeySchema> ,
 nameonly TableStatus: Option<TableStatus> ,
 nameonly CreationDateTime: Option<string> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughputDescription> ,
 nameonly TableSizeBytes: Option<Long> ,
 nameonly ItemCount: Option<Long> ,
 nameonly TableArn: Option<String> ,
 nameonly TableId: Option<TableId> ,
 nameonly BillingModeSummary: Option<BillingModeSummary> ,
 nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexDescriptionList> ,
 nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexDescriptionList> ,
 nameonly StreamSpecification: Option<StreamSpecification> ,
 nameonly LatestStreamLabel: Option<String> ,
 nameonly LatestStreamArn: Option<StreamArn> ,
 nameonly GlobalTableVersion: Option<String> ,
 nameonly Replicas: Option<ReplicaDescriptionList> ,
 nameonly RestoreSummary: Option<RestoreSummary> ,
 nameonly SSEDescription: Option<SSEDescription> ,
 nameonly ArchivalSummary: Option<ArchivalSummary> ,
 nameonly TableClassSummary: Option<TableClassSummary>
 )
 type TableId = string
 type TableName = x: string | IsValid_TableName(x) witness *
 predicate method IsValid_TableName(x: string) {
 ( 3 <= |x| <= 255 )
}
 type TableNameList = seq<TableName>
 datatype TableStatus =
	| CREATING
	| UPDATING
	| DELETING
	| ACTIVE
	| INACCESSIBLE_ENCRYPTION_CREDENTIALS
	| ARCHIVING
	| ARCHIVED
 datatype Tag = | Tag (
 nameonly Key: TagKeyString ,
 nameonly Value: TagValueString
 )
 type TagKeyList = seq<TagKeyString>
 type TagKeyString = x: string | IsValid_TagKeyString(x) witness *
 predicate method IsValid_TagKeyString(x: string) {
 ( 1 <= |x| <= 128 )
}
 type TagList = seq<Tag>
 datatype TagResourceInput = | TagResourceInput (
 nameonly ResourceArn: ResourceArnString ,
 nameonly Tags: TagList
 )
 type TagValueString = x: string | IsValid_TagValueString(x) witness *
 predicate method IsValid_TagValueString(x: string) {
 ( 0 <= |x| <= 256 )
}
 type TimeToLiveAttributeName = x: string | IsValid_TimeToLiveAttributeName(x) witness *
 predicate method IsValid_TimeToLiveAttributeName(x: string) {
 ( 1 <= |x| <= 255 )
}
 datatype TimeToLiveDescription = | TimeToLiveDescription (
 nameonly TimeToLiveStatus: Option<TimeToLiveStatus> ,
 nameonly AttributeName: Option<TimeToLiveAttributeName>
 )
 type TimeToLiveEnabled = bool
 datatype TimeToLiveSpecification = | TimeToLiveSpecification (
 nameonly Enabled: TimeToLiveEnabled ,
 nameonly AttributeName: TimeToLiveAttributeName
 )
 datatype TimeToLiveStatus =
	| ENABLING
	| DISABLING
	| ENABLED
	| DISABLED
 datatype TransactGetItem = | TransactGetItem (
 nameonly Get: Get
 )
 type TransactGetItemList = x: seq<TransactGetItem> | IsValid_TransactGetItemList(x) witness *
 predicate method IsValid_TransactGetItemList(x: seq<TransactGetItem>) {
 ( 1 <= |x| <= 25 )
}
 datatype TransactGetItemsInput = | TransactGetItemsInput (
 nameonly TransactItems: TransactGetItemList ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity>
 )
 datatype TransactGetItemsOutput = | TransactGetItemsOutput (
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> ,
 nameonly Responses: Option<ItemResponseList>
 )
 datatype TransactWriteItem = | TransactWriteItem (
 nameonly ConditionCheck: Option<ConditionCheck> ,
 nameonly Put: Option<Put> ,
 nameonly Delete: Option<Delete> ,
 nameonly Update: Option<Update>
 )
 type TransactWriteItemList = x: seq<TransactWriteItem> | IsValid_TransactWriteItemList(x) witness *
 predicate method IsValid_TransactWriteItemList(x: seq<TransactWriteItem>) {
 ( 1 <= |x| <= 25 )
}
 datatype TransactWriteItemsInput = | TransactWriteItemsInput (
 nameonly TransactItems: TransactWriteItemList ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> ,
 nameonly ClientRequestToken: Option<ClientRequestToken>
 )
 datatype TransactWriteItemsOutput = | TransactWriteItemsOutput (
 nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> ,
 nameonly ItemCollectionMetrics: Option<ItemCollectionMetricsPerTable>
 )
 datatype UntagResourceInput = | UntagResourceInput (
 nameonly ResourceArn: ResourceArnString ,
 nameonly TagKeys: TagKeyList
 )
 datatype Update = | Update (
 nameonly Key: Key ,
 nameonly UpdateExpression: UpdateExpression ,
 nameonly TableName: TableName ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> ,
 nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure>
 )
 datatype UpdateContinuousBackupsInput = | UpdateContinuousBackupsInput (
 nameonly TableName: TableName ,
 nameonly PointInTimeRecoverySpecification: PointInTimeRecoverySpecification
 )
 datatype UpdateContinuousBackupsOutput = | UpdateContinuousBackupsOutput (
 nameonly ContinuousBackupsDescription: Option<ContinuousBackupsDescription>
 )
 datatype UpdateContributorInsightsInput = | UpdateContributorInsightsInput (
 nameonly TableName: TableName ,
 nameonly IndexName: Option<IndexName> ,
 nameonly ContributorInsightsAction: ContributorInsightsAction
 )
 datatype UpdateContributorInsightsOutput = | UpdateContributorInsightsOutput (
 nameonly TableName: Option<TableName> ,
 nameonly IndexName: Option<IndexName> ,
 nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus>
 )
 type UpdateExpression = string
 datatype UpdateGlobalSecondaryIndexAction = | UpdateGlobalSecondaryIndexAction (
 nameonly IndexName: IndexName ,
 nameonly ProvisionedThroughput: ProvisionedThroughput
 )
 datatype UpdateGlobalTableInput = | UpdateGlobalTableInput (
 nameonly GlobalTableName: TableName ,
 nameonly ReplicaUpdates: ReplicaUpdateList
 )
 datatype UpdateGlobalTableOutput = | UpdateGlobalTableOutput (
 nameonly GlobalTableDescription: Option<GlobalTableDescription>
 )
 datatype UpdateGlobalTableSettingsInput = | UpdateGlobalTableSettingsInput (
 nameonly GlobalTableName: TableName ,
 nameonly GlobalTableBillingMode: Option<BillingMode> ,
 nameonly GlobalTableProvisionedWriteCapacityUnits: Option<PositiveLongObject> ,
 nameonly GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> ,
 nameonly GlobalTableGlobalSecondaryIndexSettingsUpdate: Option<GlobalTableGlobalSecondaryIndexSettingsUpdateList> ,
 nameonly ReplicaSettingsUpdate: Option<ReplicaSettingsUpdateList>
 )
 datatype UpdateGlobalTableSettingsOutput = | UpdateGlobalTableSettingsOutput (
 nameonly GlobalTableName: Option<TableName> ,
 nameonly ReplicaSettings: Option<ReplicaSettingsDescriptionList>
 )
 datatype UpdateItemInput = | UpdateItemInput (
 nameonly TableName: TableName ,
 nameonly Key: Key ,
 nameonly AttributeUpdates: Option<AttributeUpdates> ,
 nameonly Expected: Option<ExpectedAttributeMap> ,
 nameonly ConditionalOperator: Option<ConditionalOperator> ,
 nameonly ReturnValues: Option<ReturnValue> ,
 nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> ,
 nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> ,
 nameonly UpdateExpression: Option<UpdateExpression> ,
 nameonly ConditionExpression: Option<ConditionExpression> ,
 nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> ,
 nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap>
 )
 datatype UpdateItemOutput = | UpdateItemOutput (
 nameonly Attributes: Option<AttributeMap> ,
 nameonly ConsumedCapacity: Option<ConsumedCapacity> ,
 nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics>
 )
 datatype UpdateReplicationGroupMemberAction = | UpdateReplicationGroupMemberAction (
 nameonly RegionName: RegionName ,
 nameonly KMSMasterKeyId: Option<KMSMasterKeyId> ,
 nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> ,
 nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexList> ,
 nameonly TableClassOverride: Option<TableClass>
 )
 datatype UpdateTableInput = | UpdateTableInput (
 nameonly AttributeDefinitions: Option<AttributeDefinitions> ,
 nameonly TableName: TableName ,
 nameonly BillingMode: Option<BillingMode> ,
 nameonly ProvisionedThroughput: Option<ProvisionedThroughput> ,
 nameonly GlobalSecondaryIndexUpdates: Option<GlobalSecondaryIndexUpdateList> ,
 nameonly StreamSpecification: Option<StreamSpecification> ,
 nameonly SSESpecification: Option<SSESpecification> ,
 nameonly ReplicaUpdates: Option<ReplicationGroupUpdateList> ,
 nameonly TableClass: Option<TableClass>
 )
 datatype UpdateTableOutput = | UpdateTableOutput (
 nameonly TableDescription: Option<TableDescription>
 )
 datatype UpdateTableReplicaAutoScalingInput = | UpdateTableReplicaAutoScalingInput (
 nameonly GlobalSecondaryIndexUpdates: Option<GlobalSecondaryIndexAutoScalingUpdateList> ,
 nameonly TableName: TableName ,
 nameonly ProvisionedWriteCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate> ,
 nameonly ReplicaUpdates: Option<ReplicaAutoScalingUpdateList>
 )
 datatype UpdateTableReplicaAutoScalingOutput = | UpdateTableReplicaAutoScalingOutput (
 nameonly TableAutoScalingDescription: Option<TableAutoScalingDescription>
 )
 datatype UpdateTimeToLiveInput = | UpdateTimeToLiveInput (
 nameonly TableName: TableName ,
 nameonly TimeToLiveSpecification: TimeToLiveSpecification
 )
 datatype UpdateTimeToLiveOutput = | UpdateTimeToLiveOutput (
 nameonly TimeToLiveSpecification: Option<TimeToLiveSpecification>
 )
 datatype WriteRequest = | WriteRequest (
 nameonly PutRequest: Option<PutRequest> ,
 nameonly DeleteRequest: Option<DeleteRequest>
 )
 type WriteRequests = x: seq<WriteRequest> | IsValid_WriteRequests(x) witness *
 predicate method IsValid_WriteRequests(x: seq<WriteRequest>) {
 ( 1 <= |x| <= 25 )
}
 datatype Error =
 // Local Error structures are listed here
 | BackupInUseException (
 nameonly message: Option<ErrorMessage>
 )
 | BackupNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | ConditionalCheckFailedException (
 nameonly message: Option<ErrorMessage>
 )
 | ContinuousBackupsUnavailableException (
 nameonly message: Option<ErrorMessage>
 )
 | DuplicateItemException (
 nameonly message: Option<ErrorMessage>
 )
 | ExportConflictException (
 nameonly message: Option<ErrorMessage>
 )
 | ExportNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | GlobalTableAlreadyExistsException (
 nameonly message: Option<ErrorMessage>
 )
 | GlobalTableNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | IdempotentParameterMismatchException (
 nameonly Message: Option<ErrorMessage>
 )
 | ImportConflictException (
 nameonly message: Option<ErrorMessage>
 )
 | ImportNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | IndexNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | InternalServerError (
 nameonly message: Option<ErrorMessage>
 )
 | InvalidEndpointException (
 nameonly Message: Option<String>
 )
 | InvalidExportTimeException (
 nameonly message: Option<ErrorMessage>
 )
 | InvalidRestoreTimeException (
 nameonly message: Option<ErrorMessage>
 )
 | ItemCollectionSizeLimitExceededException (
 nameonly message: Option<ErrorMessage>
 )
 | LimitExceededException (
 nameonly message: Option<ErrorMessage>
 )
 | PointInTimeRecoveryUnavailableException (
 nameonly message: Option<ErrorMessage>
 )
 | ProvisionedThroughputExceededException (
 nameonly message: Option<ErrorMessage>
 )
 | ReplicaAlreadyExistsException (
 nameonly message: Option<ErrorMessage>
 )
 | ReplicaNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | RequestLimitExceeded (
 nameonly message: Option<ErrorMessage>
 )
 | ResourceInUseException (
 nameonly message: Option<ErrorMessage>
 )
 | ResourceNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | TableAlreadyExistsException (
 nameonly message: Option<ErrorMessage>
 )
 | TableInUseException (
 nameonly message: Option<ErrorMessage>
 )
 | TableNotFoundException (
 nameonly message: Option<ErrorMessage>
 )
 | TransactionCanceledException (
 nameonly Message: Option<ErrorMessage> ,
 nameonly CancellationReasons: Option<CancellationReasonList>
 )
 | TransactionConflictException (
 nameonly message: Option<ErrorMessage>
 )
 | TransactionInProgressException (
 nameonly Message: Option<ErrorMessage>
 )
 // Any dependent models are listed here
 
 // The Collection error is used to collect several errors together
 // This is useful when composing OR logic.
 // Consider the following method:
 // 
 // method FN<I, O>(n:I)
 //   returns (res: Result<O, Types.Error>)
 //   ensures A(I).Success? ==> res.Success?
 //   ensures B(I).Success? ==> res.Success?
 //   ensures A(I).Failure? && B(I).Failure? ==> res.Failure?
 // 
 // If either A || B is successful then FN is successful.
 // And if A && B fail then FN will fail.
 // But what information should FN transmit back to the caller?
 // While it may be correct to hide these details from the caller,
 // this can not be the globally correct option.
 // Suppose that A and B can be blocked by different ACLs,
 // and that their representation of I is only eventually consistent.
 // How can the caller distinguish, at a minimum for logging,
 // the difference between the four failure modes?
 // || (!access(A(I)) && !access(B(I)))
 // || (!exit(A(I)) && !exit(B(I)))
 // || (!access(A(I)) && !exit(B(I)))
 // || (!exit(A(I)) && !access(B(I)))
 | CollectionOfErrors(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractComAmazonawsDynamodbService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ComAmazonawsDynamodbTypes
 datatype DynamoDBClientConfigType = DynamoDBClientConfigType
 function method DefaultDynamoDBClientConfigType(): DynamoDBClientConfigType
 method {:extern} DynamoDBClient()
 returns (res: Result<IDynamoDB_20120810Client, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
 abstract module AbstractComAmazonawsDynamodbOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ComAmazonawsDynamodbTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate BatchExecuteStatementEnsuresPublicly(input: BatchExecuteStatementInput , output: Result<BatchExecuteStatementOutput, Error>)
 // The private method to be refined by the library developer


 method BatchExecuteStatement ( config: InternalConfig , input: BatchExecuteStatementInput )
 returns (output: Result<BatchExecuteStatementOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures BatchExecuteStatementEnsuresPublicly(input, output)


 predicate BatchGetItemEnsuresPublicly(input: BatchGetItemInput , output: Result<BatchGetItemOutput, Error>)
 // The private method to be refined by the library developer


 method BatchGetItem ( config: InternalConfig , input: BatchGetItemInput )
 returns (output: Result<BatchGetItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures BatchGetItemEnsuresPublicly(input, output)


 predicate BatchWriteItemEnsuresPublicly(input: BatchWriteItemInput , output: Result<BatchWriteItemOutput, Error>)
 // The private method to be refined by the library developer


 method BatchWriteItem ( config: InternalConfig , input: BatchWriteItemInput )
 returns (output: Result<BatchWriteItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures BatchWriteItemEnsuresPublicly(input, output)


 predicate CreateBackupEnsuresPublicly(input: CreateBackupInput , output: Result<CreateBackupOutput, Error>)
 // The private method to be refined by the library developer


 method CreateBackup ( config: InternalConfig , input: CreateBackupInput )
 returns (output: Result<CreateBackupOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures CreateBackupEnsuresPublicly(input, output)


 predicate CreateGlobalTableEnsuresPublicly(input: CreateGlobalTableInput , output: Result<CreateGlobalTableOutput, Error>)
 // The private method to be refined by the library developer


 method CreateGlobalTable ( config: InternalConfig , input: CreateGlobalTableInput )
 returns (output: Result<CreateGlobalTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures CreateGlobalTableEnsuresPublicly(input, output)


 predicate CreateTableEnsuresPublicly(input: CreateTableInput , output: Result<CreateTableOutput, Error>)
 // The private method to be refined by the library developer


 method CreateTable ( config: InternalConfig , input: CreateTableInput )
 returns (output: Result<CreateTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures CreateTableEnsuresPublicly(input, output)


 predicate DeleteBackupEnsuresPublicly(input: DeleteBackupInput , output: Result<DeleteBackupOutput, Error>)
 // The private method to be refined by the library developer


 method DeleteBackup ( config: InternalConfig , input: DeleteBackupInput )
 returns (output: Result<DeleteBackupOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DeleteBackupEnsuresPublicly(input, output)


 predicate DeleteItemEnsuresPublicly(input: DeleteItemInput , output: Result<DeleteItemOutput, Error>)
 // The private method to be refined by the library developer


 method DeleteItem ( config: InternalConfig , input: DeleteItemInput )
 returns (output: Result<DeleteItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DeleteItemEnsuresPublicly(input, output)


 predicate DeleteTableEnsuresPublicly(input: DeleteTableInput , output: Result<DeleteTableOutput, Error>)
 // The private method to be refined by the library developer


 method DeleteTable ( config: InternalConfig , input: DeleteTableInput )
 returns (output: Result<DeleteTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DeleteTableEnsuresPublicly(input, output)


 predicate DescribeBackupEnsuresPublicly(input: DescribeBackupInput , output: Result<DescribeBackupOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeBackup ( config: InternalConfig , input: DescribeBackupInput )
 returns (output: Result<DescribeBackupOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeBackupEnsuresPublicly(input, output)


 predicate DescribeContinuousBackupsEnsuresPublicly(input: DescribeContinuousBackupsInput , output: Result<DescribeContinuousBackupsOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeContinuousBackups ( config: InternalConfig , input: DescribeContinuousBackupsInput )
 returns (output: Result<DescribeContinuousBackupsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeContinuousBackupsEnsuresPublicly(input, output)


 predicate DescribeContributorInsightsEnsuresPublicly(input: DescribeContributorInsightsInput , output: Result<DescribeContributorInsightsOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeContributorInsights ( config: InternalConfig , input: DescribeContributorInsightsInput )
 returns (output: Result<DescribeContributorInsightsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeContributorInsightsEnsuresPublicly(input, output)


 predicate DescribeEndpointsEnsuresPublicly(input: DescribeEndpointsRequest , output: Result<DescribeEndpointsResponse, Error>)
 // The private method to be refined by the library developer


 method DescribeEndpoints ( config: InternalConfig , input: DescribeEndpointsRequest )
 returns (output: Result<DescribeEndpointsResponse, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeEndpointsEnsuresPublicly(input, output)


 predicate DescribeExportEnsuresPublicly(input: DescribeExportInput , output: Result<DescribeExportOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeExport ( config: InternalConfig , input: DescribeExportInput )
 returns (output: Result<DescribeExportOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeExportEnsuresPublicly(input, output)


 predicate DescribeGlobalTableEnsuresPublicly(input: DescribeGlobalTableInput , output: Result<DescribeGlobalTableOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeGlobalTable ( config: InternalConfig , input: DescribeGlobalTableInput )
 returns (output: Result<DescribeGlobalTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeGlobalTableEnsuresPublicly(input, output)


 predicate DescribeGlobalTableSettingsEnsuresPublicly(input: DescribeGlobalTableSettingsInput , output: Result<DescribeGlobalTableSettingsOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeGlobalTableSettings ( config: InternalConfig , input: DescribeGlobalTableSettingsInput )
 returns (output: Result<DescribeGlobalTableSettingsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeGlobalTableSettingsEnsuresPublicly(input, output)


 predicate DescribeImportEnsuresPublicly(input: DescribeImportInput , output: Result<DescribeImportOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeImport ( config: InternalConfig , input: DescribeImportInput )
 returns (output: Result<DescribeImportOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeImportEnsuresPublicly(input, output)


 predicate DescribeKinesisStreamingDestinationEnsuresPublicly(input: DescribeKinesisStreamingDestinationInput , output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeKinesisStreamingDestination ( config: InternalConfig , input: DescribeKinesisStreamingDestinationInput )
 returns (output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeKinesisStreamingDestinationEnsuresPublicly(input, output)


 predicate DescribeLimitsEnsuresPublicly(input: DescribeLimitsInput , output: Result<DescribeLimitsOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeLimits ( config: InternalConfig , input: DescribeLimitsInput )
 returns (output: Result<DescribeLimitsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeLimitsEnsuresPublicly(input, output)


 predicate DescribeTableEnsuresPublicly(input: DescribeTableInput , output: Result<DescribeTableOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeTable ( config: InternalConfig , input: DescribeTableInput )
 returns (output: Result<DescribeTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeTableEnsuresPublicly(input, output)


 predicate DescribeTableReplicaAutoScalingEnsuresPublicly(input: DescribeTableReplicaAutoScalingInput , output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeTableReplicaAutoScaling ( config: InternalConfig , input: DescribeTableReplicaAutoScalingInput )
 returns (output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeTableReplicaAutoScalingEnsuresPublicly(input, output)


 predicate DescribeTimeToLiveEnsuresPublicly(input: DescribeTimeToLiveInput , output: Result<DescribeTimeToLiveOutput, Error>)
 // The private method to be refined by the library developer


 method DescribeTimeToLive ( config: InternalConfig , input: DescribeTimeToLiveInput )
 returns (output: Result<DescribeTimeToLiveOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DescribeTimeToLiveEnsuresPublicly(input, output)


 predicate DisableKinesisStreamingDestinationEnsuresPublicly(input: DisableKinesisStreamingDestinationInput , output: Result<DisableKinesisStreamingDestinationOutput, Error>)
 // The private method to be refined by the library developer


 method DisableKinesisStreamingDestination ( config: InternalConfig , input: DisableKinesisStreamingDestinationInput )
 returns (output: Result<DisableKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DisableKinesisStreamingDestinationEnsuresPublicly(input, output)


 predicate EnableKinesisStreamingDestinationEnsuresPublicly(input: EnableKinesisStreamingDestinationInput , output: Result<EnableKinesisStreamingDestinationOutput, Error>)
 // The private method to be refined by the library developer


 method EnableKinesisStreamingDestination ( config: InternalConfig , input: EnableKinesisStreamingDestinationInput )
 returns (output: Result<EnableKinesisStreamingDestinationOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures EnableKinesisStreamingDestinationEnsuresPublicly(input, output)


 predicate ExecuteStatementEnsuresPublicly(input: ExecuteStatementInput , output: Result<ExecuteStatementOutput, Error>)
 // The private method to be refined by the library developer


 method ExecuteStatement ( config: InternalConfig , input: ExecuteStatementInput )
 returns (output: Result<ExecuteStatementOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ExecuteStatementEnsuresPublicly(input, output)


 predicate ExecuteTransactionEnsuresPublicly(input: ExecuteTransactionInput , output: Result<ExecuteTransactionOutput, Error>)
 // The private method to be refined by the library developer


 method ExecuteTransaction ( config: InternalConfig , input: ExecuteTransactionInput )
 returns (output: Result<ExecuteTransactionOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ExecuteTransactionEnsuresPublicly(input, output)


 predicate ExportTableToPointInTimeEnsuresPublicly(input: ExportTableToPointInTimeInput , output: Result<ExportTableToPointInTimeOutput, Error>)
 // The private method to be refined by the library developer


 method ExportTableToPointInTime ( config: InternalConfig , input: ExportTableToPointInTimeInput )
 returns (output: Result<ExportTableToPointInTimeOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ExportTableToPointInTimeEnsuresPublicly(input, output)


 predicate GetItemEnsuresPublicly(input: GetItemInput , output: Result<GetItemOutput, Error>)
 // The private method to be refined by the library developer


 method GetItem ( config: InternalConfig , input: GetItemInput )
 returns (output: Result<GetItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetItemEnsuresPublicly(input, output)


 predicate ImportTableEnsuresPublicly(input: ImportTableInput , output: Result<ImportTableOutput, Error>)
 // The private method to be refined by the library developer


 method ImportTable ( config: InternalConfig , input: ImportTableInput )
 returns (output: Result<ImportTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ImportTableEnsuresPublicly(input, output)


 predicate ListBackupsEnsuresPublicly(input: ListBackupsInput , output: Result<ListBackupsOutput, Error>)
 // The private method to be refined by the library developer


 method ListBackups ( config: InternalConfig , input: ListBackupsInput )
 returns (output: Result<ListBackupsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListBackupsEnsuresPublicly(input, output)


 predicate ListContributorInsightsEnsuresPublicly(input: ListContributorInsightsInput , output: Result<ListContributorInsightsOutput, Error>)
 // The private method to be refined by the library developer


 method ListContributorInsights ( config: InternalConfig , input: ListContributorInsightsInput )
 returns (output: Result<ListContributorInsightsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListContributorInsightsEnsuresPublicly(input, output)


 predicate ListExportsEnsuresPublicly(input: ListExportsInput , output: Result<ListExportsOutput, Error>)
 // The private method to be refined by the library developer


 method ListExports ( config: InternalConfig , input: ListExportsInput )
 returns (output: Result<ListExportsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListExportsEnsuresPublicly(input, output)


 predicate ListGlobalTablesEnsuresPublicly(input: ListGlobalTablesInput , output: Result<ListGlobalTablesOutput, Error>)
 // The private method to be refined by the library developer


 method ListGlobalTables ( config: InternalConfig , input: ListGlobalTablesInput )
 returns (output: Result<ListGlobalTablesOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListGlobalTablesEnsuresPublicly(input, output)


 predicate ListImportsEnsuresPublicly(input: ListImportsInput , output: Result<ListImportsOutput, Error>)
 // The private method to be refined by the library developer


 method ListImports ( config: InternalConfig , input: ListImportsInput )
 returns (output: Result<ListImportsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListImportsEnsuresPublicly(input, output)


 predicate ListTablesEnsuresPublicly(input: ListTablesInput , output: Result<ListTablesOutput, Error>)
 // The private method to be refined by the library developer


 method ListTables ( config: InternalConfig , input: ListTablesInput )
 returns (output: Result<ListTablesOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListTablesEnsuresPublicly(input, output)


 predicate ListTagsOfResourceEnsuresPublicly(input: ListTagsOfResourceInput , output: Result<ListTagsOfResourceOutput, Error>)
 // The private method to be refined by the library developer


 method ListTagsOfResource ( config: InternalConfig , input: ListTagsOfResourceInput )
 returns (output: Result<ListTagsOfResourceOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ListTagsOfResourceEnsuresPublicly(input, output)


 predicate PutItemEnsuresPublicly(input: PutItemInput , output: Result<PutItemOutput, Error>)
 // The private method to be refined by the library developer


 method PutItem ( config: InternalConfig , input: PutItemInput )
 returns (output: Result<PutItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures PutItemEnsuresPublicly(input, output)


 predicate QueryEnsuresPublicly(input: QueryInput , output: Result<QueryOutput, Error>)
 // The private method to be refined by the library developer


 method Query ( config: InternalConfig , input: QueryInput )
 returns (output: Result<QueryOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures QueryEnsuresPublicly(input, output)


 predicate RestoreTableFromBackupEnsuresPublicly(input: RestoreTableFromBackupInput , output: Result<RestoreTableFromBackupOutput, Error>)
 // The private method to be refined by the library developer


 method RestoreTableFromBackup ( config: InternalConfig , input: RestoreTableFromBackupInput )
 returns (output: Result<RestoreTableFromBackupOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures RestoreTableFromBackupEnsuresPublicly(input, output)


 predicate RestoreTableToPointInTimeEnsuresPublicly(input: RestoreTableToPointInTimeInput , output: Result<RestoreTableToPointInTimeOutput, Error>)
 // The private method to be refined by the library developer


 method RestoreTableToPointInTime ( config: InternalConfig , input: RestoreTableToPointInTimeInput )
 returns (output: Result<RestoreTableToPointInTimeOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures RestoreTableToPointInTimeEnsuresPublicly(input, output)


 predicate ScanEnsuresPublicly(input: ScanInput , output: Result<ScanOutput, Error>)
 // The private method to be refined by the library developer


 method Scan ( config: InternalConfig , input: ScanInput )
 returns (output: Result<ScanOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ScanEnsuresPublicly(input, output)


 predicate TagResourceEnsuresPublicly(input: TagResourceInput , output: Result<(), Error>)
 // The private method to be refined by the library developer


 method TagResource ( config: InternalConfig , input: TagResourceInput )
 returns (output: Result<(), Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures TagResourceEnsuresPublicly(input, output)


 predicate TransactGetItemsEnsuresPublicly(input: TransactGetItemsInput , output: Result<TransactGetItemsOutput, Error>)
 // The private method to be refined by the library developer


 method TransactGetItems ( config: InternalConfig , input: TransactGetItemsInput )
 returns (output: Result<TransactGetItemsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures TransactGetItemsEnsuresPublicly(input, output)


 predicate TransactWriteItemsEnsuresPublicly(input: TransactWriteItemsInput , output: Result<TransactWriteItemsOutput, Error>)
 // The private method to be refined by the library developer


 method TransactWriteItems ( config: InternalConfig , input: TransactWriteItemsInput )
 returns (output: Result<TransactWriteItemsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures TransactWriteItemsEnsuresPublicly(input, output)


 predicate UntagResourceEnsuresPublicly(input: UntagResourceInput , output: Result<(), Error>)
 // The private method to be refined by the library developer


 method UntagResource ( config: InternalConfig , input: UntagResourceInput )
 returns (output: Result<(), Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UntagResourceEnsuresPublicly(input, output)


 predicate UpdateContinuousBackupsEnsuresPublicly(input: UpdateContinuousBackupsInput , output: Result<UpdateContinuousBackupsOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateContinuousBackups ( config: InternalConfig , input: UpdateContinuousBackupsInput )
 returns (output: Result<UpdateContinuousBackupsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateContinuousBackupsEnsuresPublicly(input, output)


 predicate UpdateContributorInsightsEnsuresPublicly(input: UpdateContributorInsightsInput , output: Result<UpdateContributorInsightsOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateContributorInsights ( config: InternalConfig , input: UpdateContributorInsightsInput )
 returns (output: Result<UpdateContributorInsightsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateContributorInsightsEnsuresPublicly(input, output)


 predicate UpdateGlobalTableEnsuresPublicly(input: UpdateGlobalTableInput , output: Result<UpdateGlobalTableOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateGlobalTable ( config: InternalConfig , input: UpdateGlobalTableInput )
 returns (output: Result<UpdateGlobalTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateGlobalTableEnsuresPublicly(input, output)


 predicate UpdateGlobalTableSettingsEnsuresPublicly(input: UpdateGlobalTableSettingsInput , output: Result<UpdateGlobalTableSettingsOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateGlobalTableSettings ( config: InternalConfig , input: UpdateGlobalTableSettingsInput )
 returns (output: Result<UpdateGlobalTableSettingsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateGlobalTableSettingsEnsuresPublicly(input, output)


 predicate UpdateItemEnsuresPublicly(input: UpdateItemInput , output: Result<UpdateItemOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateItem ( config: InternalConfig , input: UpdateItemInput )
 returns (output: Result<UpdateItemOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateItemEnsuresPublicly(input, output)


 predicate UpdateTableEnsuresPublicly(input: UpdateTableInput , output: Result<UpdateTableOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateTable ( config: InternalConfig , input: UpdateTableInput )
 returns (output: Result<UpdateTableOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateTableEnsuresPublicly(input, output)


 predicate UpdateTableReplicaAutoScalingEnsuresPublicly(input: UpdateTableReplicaAutoScalingInput , output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateTableReplicaAutoScaling ( config: InternalConfig , input: UpdateTableReplicaAutoScalingInput )
 returns (output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateTableReplicaAutoScalingEnsuresPublicly(input, output)


 predicate UpdateTimeToLiveEnsuresPublicly(input: UpdateTimeToLiveInput , output: Result<UpdateTimeToLiveOutput, Error>)
 // The private method to be refined by the library developer


 method UpdateTimeToLive ( config: InternalConfig , input: UpdateTimeToLiveInput )
 returns (output: Result<UpdateTimeToLiveOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UpdateTimeToLiveEnsuresPublicly(input, output)
}
