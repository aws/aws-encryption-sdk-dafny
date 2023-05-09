// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic; namespace Com.Amazonaws.Dynamodb {
 public class DynamoDBv2Shim : software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient {
 public Amazon.DynamoDBv2.AmazonDynamoDBClient _impl;
 public DynamoDBv2Shim(Amazon.DynamoDBv2.AmazonDynamoDBClient impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> BatchExecuteStatement(software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchExecuteStatementInput request) {
 Amazon.DynamoDBv2.Model.BatchExecuteStatementRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S26_BatchExecuteStatementInput(request); try {
 Amazon.DynamoDBv2.Model.BatchExecuteStatementResponse sdkResponse =
 this._impl.BatchExecuteStatementAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S27_BatchExecuteStatementOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> BatchGetItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchGetItemInput request) {
 Amazon.DynamoDBv2.Model.BatchGetItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_BatchGetItemInput(request); try {
 Amazon.DynamoDBv2.Model.BatchGetItemResponse sdkResponse =
 this._impl.BatchGetItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_BatchGetItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchWriteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> BatchWriteItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchWriteItemInput request) {
 Amazon.DynamoDBv2.Model.BatchWriteItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_BatchWriteItemInput(request); try {
 Amazon.DynamoDBv2.Model.BatchWriteItemResponse sdkResponse =
 this._impl.BatchWriteItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchWriteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_BatchWriteItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IBatchWriteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> CreateBackup(software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateBackupInput request) {
 Amazon.DynamoDBv2.Model.CreateBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_CreateBackupInput(request); try {
 Amazon.DynamoDBv2.Model.CreateBackupResponse sdkResponse =
 this._impl.CreateBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_CreateBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> CreateGlobalTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.CreateGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_CreateGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.CreateGlobalTableResponse sdkResponse =
 this._impl.CreateGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_CreateGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> CreateTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateTableInput request) {
 Amazon.DynamoDBv2.Model.CreateTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_CreateTableInput(request); try {
 Amazon.DynamoDBv2.Model.CreateTableResponse sdkResponse =
 this._impl.CreateTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_CreateTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ICreateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DeleteBackup(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteBackupInput request) {
 Amazon.DynamoDBv2.Model.DeleteBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_DeleteBackupInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteBackupResponse sdkResponse =
 this._impl.DeleteBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_DeleteBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DeleteItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemInput request) {
 Amazon.DynamoDBv2.Model.DeleteItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_DeleteItemInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteItemResponse sdkResponse =
 this._impl.DeleteItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_DeleteItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DeleteTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteTableInput request) {
 Amazon.DynamoDBv2.Model.DeleteTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_DeleteTableInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteTableResponse sdkResponse =
 this._impl.DeleteTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_DeleteTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeBackup(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeBackupInput request) {
 Amazon.DynamoDBv2.Model.DescribeBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeBackupInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeBackupResponse sdkResponse =
 this._impl.DescribeBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeContinuousBackups(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContinuousBackupsInput request) {
 Amazon.DynamoDBv2.Model.DescribeContinuousBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_DescribeContinuousBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeContinuousBackupsResponse sdkResponse =
 this._impl.DescribeContinuousBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_DescribeContinuousBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeContributorInsights(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.DescribeContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S32_DescribeContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeContributorInsightsResponse sdkResponse =
 this._impl.DescribeContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S33_DescribeContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeEndpointsResponse, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeEndpoints(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeEndpointsRequest request) {
 Amazon.DynamoDBv2.Model.DescribeEndpointsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeEndpointsRequest(request); try {
 Amazon.DynamoDBv2.Model.DescribeEndpointsResponse sdkResponse =
 this._impl.DescribeEndpointsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeEndpointsResponse, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S25_DescribeEndpointsResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeEndpointsResponse, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeExportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeExport(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeExportInput request) {
 Amazon.DynamoDBv2.Model.DescribeExportRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeExportInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeExportResponse sdkResponse =
 this._impl.DescribeExportAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeExportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeExportOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeExportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeGlobalTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableResponse sdkResponse =
 this._impl.DescribeGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S25_DescribeGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeGlobalTableSettings(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableSettingsInput request) {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableSettingsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S32_DescribeGlobalTableSettingsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableSettingsResponse sdkResponse =
 this._impl.DescribeGlobalTableSettingsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S33_DescribeGlobalTableSettingsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeImportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeImport(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeImportInput request) {
 Amazon.DynamoDBv2.Model.DescribeImportRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeImportInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeImportResponse sdkResponse =
 this._impl.DescribeImportAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeImportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeImportOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeImportOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeKinesisStreamingDestination(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.DescribeKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S40_DescribeKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeKinesisStreamingDestinationResponse sdkResponse =
 this._impl.DescribeKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S41_DescribeKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeLimitsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeLimits(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeLimitsInput request) {
 Amazon.DynamoDBv2.Model.DescribeLimitsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeLimitsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeLimitsResponse sdkResponse =
 this._impl.DescribeLimitsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeLimitsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeLimitsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeLimitsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableInput request) {
 Amazon.DynamoDBv2.Model.DescribeTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_DescribeTableInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTableResponse sdkResponse =
 this._impl.DescribeTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeTableReplicaAutoScaling(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableReplicaAutoScalingInput request) {
 Amazon.DynamoDBv2.Model.DescribeTableReplicaAutoScalingRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S36_DescribeTableReplicaAutoScalingInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTableReplicaAutoScalingResponse sdkResponse =
 this._impl.DescribeTableReplicaAutoScalingAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S37_DescribeTableReplicaAutoScalingOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DescribeTimeToLive(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTimeToLiveInput request) {
 Amazon.DynamoDBv2.Model.DescribeTimeToLiveRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_DescribeTimeToLiveInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTimeToLiveResponse sdkResponse =
 this._impl.DescribeTimeToLiveAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeTimeToLiveOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDescribeTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDisableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> DisableKinesisStreamingDestination(software.amazon.cryptography.services.dynamodb.internaldafny.types._IDisableKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.DisableKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S39_DisableKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.DisableKinesisStreamingDestinationResponse sdkResponse =
 this._impl.DisableKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDisableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S40_DisableKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDisableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IEnableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> EnableKinesisStreamingDestination(software.amazon.cryptography.services.dynamodb.internaldafny.types._IEnableKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.EnableKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S38_EnableKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.EnableKinesisStreamingDestinationResponse sdkResponse =
 this._impl.EnableKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IEnableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S39_EnableKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IEnableKinesisStreamingDestinationOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ExecuteStatement(software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteStatementInput request) {
 Amazon.DynamoDBv2.Model.ExecuteStatementRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_ExecuteStatementInput(request); try {
 Amazon.DynamoDBv2.Model.ExecuteStatementResponse sdkResponse =
 this._impl.ExecuteStatementAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_ExecuteStatementOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteStatementOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteTransactionOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ExecuteTransaction(software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteTransactionInput request) {
 Amazon.DynamoDBv2.Model.ExecuteTransactionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_ExecuteTransactionInput(request); try {
 Amazon.DynamoDBv2.Model.ExecuteTransactionResponse sdkResponse =
 this._impl.ExecuteTransactionAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteTransactionOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_ExecuteTransactionOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExecuteTransactionOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExportTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ExportTableToPointInTime(software.amazon.cryptography.services.dynamodb.internaldafny.types._IExportTableToPointInTimeInput request) {
 Amazon.DynamoDBv2.Model.ExportTableToPointInTimeRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_ExportTableToPointInTimeInput(request); try {
 Amazon.DynamoDBv2.Model.ExportTableToPointInTimeResponse sdkResponse =
 this._impl.ExportTableToPointInTimeAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExportTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_ExportTableToPointInTimeOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IExportTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> GetItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemInput request) {
 Amazon.DynamoDBv2.Model.GetItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S12_GetItemInput(request); try {
 Amazon.DynamoDBv2.Model.GetItemResponse sdkResponse =
 this._impl.GetItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S13_GetItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IImportTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ImportTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IImportTableInput request) {
 Amazon.DynamoDBv2.Model.ImportTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ImportTableInput(request); try {
 Amazon.DynamoDBv2.Model.ImportTableResponse sdkResponse =
 this._impl.ImportTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IImportTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ImportTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IImportTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListBackups(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListBackupsInput request) {
 Amazon.DynamoDBv2.Model.ListBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.ListBackupsResponse sdkResponse =
 this._impl.ListBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListContributorInsights(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.ListContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_ListContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.ListContributorInsightsResponse sdkResponse =
 this._impl.ListContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_ListContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListExportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListExports(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListExportsInput request) {
 Amazon.DynamoDBv2.Model.ListExportsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListExportsInput(request); try {
 Amazon.DynamoDBv2.Model.ListExportsResponse sdkResponse =
 this._impl.ListExportsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListExportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListExportsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListExportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListGlobalTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListGlobalTables(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListGlobalTablesInput request) {
 Amazon.DynamoDBv2.Model.ListGlobalTablesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_ListGlobalTablesInput(request); try {
 Amazon.DynamoDBv2.Model.ListGlobalTablesResponse sdkResponse =
 this._impl.ListGlobalTablesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListGlobalTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_ListGlobalTablesOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListGlobalTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListImportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListImports(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListImportsInput request) {
 Amazon.DynamoDBv2.Model.ListImportsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListImportsInput(request); try {
 Amazon.DynamoDBv2.Model.ListImportsResponse sdkResponse =
 this._impl.ListImportsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListImportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListImportsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListImportsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListTables(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTablesInput request) {
 Amazon.DynamoDBv2.Model.ListTablesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_ListTablesInput(request); try {
 Amazon.DynamoDBv2.Model.ListTablesResponse sdkResponse =
 this._impl.ListTablesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListTablesOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTablesOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTagsOfResourceOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> ListTagsOfResource(software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTagsOfResourceInput request) {
 Amazon.DynamoDBv2.Model.ListTagsOfResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_ListTagsOfResourceInput(request); try {
 Amazon.DynamoDBv2.Model.ListTagsOfResourceResponse sdkResponse =
 this._impl.ListTagsOfResourceAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTagsOfResourceOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_ListTagsOfResourceOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IListTagsOfResourceOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> PutItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemInput request) {
 Amazon.DynamoDBv2.Model.PutItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S12_PutItemInput(request); try {
 Amazon.DynamoDBv2.Model.PutItemResponse sdkResponse =
 this._impl.PutItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S13_PutItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> Query(software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryInput request) {
 Amazon.DynamoDBv2.Model.QueryRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S10_QueryInput(request); try {
 Amazon.DynamoDBv2.Model.QueryResponse sdkResponse =
 this._impl.QueryAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S11_QueryOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableFromBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> RestoreTableFromBackup(software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableFromBackupInput request) {
 Amazon.DynamoDBv2.Model.RestoreTableFromBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S27_RestoreTableFromBackupInput(request); try {
 Amazon.DynamoDBv2.Model.RestoreTableFromBackupResponse sdkResponse =
 this._impl.RestoreTableFromBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableFromBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_RestoreTableFromBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableFromBackupOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> RestoreTableToPointInTime(software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableToPointInTimeInput request) {
 Amazon.DynamoDBv2.Model.RestoreTableToPointInTimeRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_RestoreTableToPointInTimeInput(request); try {
 Amazon.DynamoDBv2.Model.RestoreTableToPointInTimeResponse sdkResponse =
 this._impl.RestoreTableToPointInTimeAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_RestoreTableToPointInTimeOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IRestoreTableToPointInTimeOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IScanOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> Scan(software.amazon.cryptography.services.dynamodb.internaldafny.types._IScanInput request) {
 Amazon.DynamoDBv2.Model.ScanRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_ScanInput(request); try {
 Amazon.DynamoDBv2.Model.ScanResponse sdkResponse =
 this._impl.ScanAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IScanOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S10_ScanOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IScanOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> TagResource(software.amazon.cryptography.services.dynamodb.internaldafny.types._ITagResourceInput request) {
 Amazon.DynamoDBv2.Model.TagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_TagResourceInput(request); try {

 this._impl.TagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactGetItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> TransactGetItems(software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactGetItemsInput request) {
 Amazon.DynamoDBv2.Model.TransactGetItemsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_TransactGetItemsInput(request); try {
 Amazon.DynamoDBv2.Model.TransactGetItemsResponse sdkResponse =
 this._impl.TransactGetItemsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactGetItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_TransactGetItemsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactGetItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> TransactWriteItems(software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsInput request) {
 Amazon.DynamoDBv2.Model.TransactWriteItemsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_TransactWriteItemsInput(request); try {
 Amazon.DynamoDBv2.Model.TransactWriteItemsResponse sdkResponse =
 this._impl.TransactWriteItemsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_TransactWriteItemsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UntagResource(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUntagResourceInput request) {
 Amazon.DynamoDBv2.Model.UntagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_UntagResourceInput(request); try {

 this._impl.UntagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateContinuousBackups(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContinuousBackupsInput request) {
 Amazon.DynamoDBv2.Model.UpdateContinuousBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_UpdateContinuousBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateContinuousBackupsResponse sdkResponse =
 this._impl.UpdateContinuousBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_UpdateContinuousBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContinuousBackupsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateContributorInsights(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.UpdateContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_UpdateContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateContributorInsightsResponse sdkResponse =
 this._impl.UpdateContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_UpdateContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateContributorInsightsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateGlobalTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_UpdateGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableResponse sdkResponse =
 this._impl.UpdateGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_UpdateGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateGlobalTableSettings(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableSettingsInput request) {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableSettingsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_UpdateGlobalTableSettingsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableSettingsResponse sdkResponse =
 this._impl.UpdateGlobalTableSettingsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_UpdateGlobalTableSettingsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateGlobalTableSettingsOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateItem(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateItemInput request) {
 Amazon.DynamoDBv2.Model.UpdateItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_UpdateItemInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateItemResponse sdkResponse =
 this._impl.UpdateItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_UpdateItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateTable(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableInput request) {
 Amazon.DynamoDBv2.Model.UpdateTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_UpdateTableInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTableResponse sdkResponse =
 this._impl.UpdateTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_UpdateTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateTableReplicaAutoScaling(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableReplicaAutoScalingInput request) {
 Amazon.DynamoDBv2.Model.UpdateTableReplicaAutoScalingRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S34_UpdateTableReplicaAutoScalingInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTableReplicaAutoScalingResponse sdkResponse =
 this._impl.UpdateTableReplicaAutoScalingAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S35_UpdateTableReplicaAutoScalingOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTableReplicaAutoScalingOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> UpdateTimeToLive(software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTimeToLiveInput request) {
 Amazon.DynamoDBv2.Model.UpdateTimeToLiveRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_UpdateTimeToLiveInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTimeToLiveResponse sdkResponse =
 this._impl.UpdateTimeToLiveAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_UpdateTimeToLiveOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.dynamodb.internaldafny.types._IUpdateTimeToLiveOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
}
}
