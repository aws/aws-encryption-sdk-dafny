// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic; namespace Com.Amazonaws.Dynamodb {
 public class DynamoDBv2Shim : Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient {
 public Amazon.DynamoDBv2.AmazonDynamoDBClient _impl;
 public DynamoDBv2Shim(Amazon.DynamoDBv2.AmazonDynamoDBClient impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> BatchExecuteStatement(Dafny.Com.Amazonaws.Dynamodb.Types._IBatchExecuteStatementInput request) {
 Amazon.DynamoDBv2.Model.BatchExecuteStatementRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S26_BatchExecuteStatementInput(request); try {
 Amazon.DynamoDBv2.Model.BatchExecuteStatementResponse sdkResponse =
 this._impl.BatchExecuteStatementAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S27_BatchExecuteStatementOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> BatchGetItem(Dafny.Com.Amazonaws.Dynamodb.Types._IBatchGetItemInput request) {
 Amazon.DynamoDBv2.Model.BatchGetItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_BatchGetItemInput(request); try {
 Amazon.DynamoDBv2.Model.BatchGetItemResponse sdkResponse =
 this._impl.BatchGetItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_BatchGetItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchWriteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> BatchWriteItem(Dafny.Com.Amazonaws.Dynamodb.Types._IBatchWriteItemInput request) {
 Amazon.DynamoDBv2.Model.BatchWriteItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_BatchWriteItemInput(request); try {
 Amazon.DynamoDBv2.Model.BatchWriteItemResponse sdkResponse =
 this._impl.BatchWriteItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchWriteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_BatchWriteItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IBatchWriteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> CreateBackup(Dafny.Com.Amazonaws.Dynamodb.Types._ICreateBackupInput request) {
 Amazon.DynamoDBv2.Model.CreateBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_CreateBackupInput(request); try {
 Amazon.DynamoDBv2.Model.CreateBackupResponse sdkResponse =
 this._impl.CreateBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_CreateBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> CreateGlobalTable(Dafny.Com.Amazonaws.Dynamodb.Types._ICreateGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.CreateGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_CreateGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.CreateGlobalTableResponse sdkResponse =
 this._impl.CreateGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_CreateGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> CreateTable(Dafny.Com.Amazonaws.Dynamodb.Types._ICreateTableInput request) {
 Amazon.DynamoDBv2.Model.CreateTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_CreateTableInput(request); try {
 Amazon.DynamoDBv2.Model.CreateTableResponse sdkResponse =
 this._impl.CreateTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_CreateTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ICreateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DeleteBackup(Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteBackupInput request) {
 Amazon.DynamoDBv2.Model.DeleteBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_DeleteBackupInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteBackupResponse sdkResponse =
 this._impl.DeleteBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_DeleteBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DeleteItem(Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteItemInput request) {
 Amazon.DynamoDBv2.Model.DeleteItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_DeleteItemInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteItemResponse sdkResponse =
 this._impl.DeleteItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_DeleteItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DeleteTable(Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteTableInput request) {
 Amazon.DynamoDBv2.Model.DeleteTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_DeleteTableInput(request); try {
 Amazon.DynamoDBv2.Model.DeleteTableResponse sdkResponse =
 this._impl.DeleteTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_DeleteTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDeleteTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeBackup(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeBackupInput request) {
 Amazon.DynamoDBv2.Model.DescribeBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeBackupInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeBackupResponse sdkResponse =
 this._impl.DescribeBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeContinuousBackups(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContinuousBackupsInput request) {
 Amazon.DynamoDBv2.Model.DescribeContinuousBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_DescribeContinuousBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeContinuousBackupsResponse sdkResponse =
 this._impl.DescribeContinuousBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_DescribeContinuousBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeContributorInsights(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.DescribeContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S32_DescribeContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeContributorInsightsResponse sdkResponse =
 this._impl.DescribeContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S33_DescribeContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeEndpointsResponse, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeEndpoints(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeEndpointsRequest request) {
 Amazon.DynamoDBv2.Model.DescribeEndpointsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeEndpointsRequest(request); try {
 Amazon.DynamoDBv2.Model.DescribeEndpointsResponse sdkResponse =
 this._impl.DescribeEndpointsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeEndpointsResponse, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S25_DescribeEndpointsResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeEndpointsResponse, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeExportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeExport(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeExportInput request) {
 Amazon.DynamoDBv2.Model.DescribeExportRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeExportInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeExportResponse sdkResponse =
 this._impl.DescribeExportAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeExportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeExportOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeExportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeGlobalTable(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableResponse sdkResponse =
 this._impl.DescribeGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S25_DescribeGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeGlobalTableSettings(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableSettingsInput request) {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableSettingsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S32_DescribeGlobalTableSettingsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeGlobalTableSettingsResponse sdkResponse =
 this._impl.DescribeGlobalTableSettingsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S33_DescribeGlobalTableSettingsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeImportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeImport(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeImportInput request) {
 Amazon.DynamoDBv2.Model.DescribeImportRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeImportInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeImportResponse sdkResponse =
 this._impl.DescribeImportAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeImportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeImportOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeImportOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeKinesisStreamingDestination(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.DescribeKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S40_DescribeKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeKinesisStreamingDestinationResponse sdkResponse =
 this._impl.DescribeKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S41_DescribeKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeLimitsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeLimits(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeLimitsInput request) {
 Amazon.DynamoDBv2.Model.DescribeLimitsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeLimitsInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeLimitsResponse sdkResponse =
 this._impl.DescribeLimitsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeLimitsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S20_DescribeLimitsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeLimitsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeTable(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableInput request) {
 Amazon.DynamoDBv2.Model.DescribeTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_DescribeTableInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTableResponse sdkResponse =
 this._impl.DescribeTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S19_DescribeTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeTableReplicaAutoScaling(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableReplicaAutoScalingInput request) {
 Amazon.DynamoDBv2.Model.DescribeTableReplicaAutoScalingRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S36_DescribeTableReplicaAutoScalingInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTableReplicaAutoScalingResponse sdkResponse =
 this._impl.DescribeTableReplicaAutoScalingAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S37_DescribeTableReplicaAutoScalingOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DescribeTimeToLive(Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTimeToLiveInput request) {
 Amazon.DynamoDBv2.Model.DescribeTimeToLiveRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_DescribeTimeToLiveInput(request); try {
 Amazon.DynamoDBv2.Model.DescribeTimeToLiveResponse sdkResponse =
 this._impl.DescribeTimeToLiveAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_DescribeTimeToLiveOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDescribeTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IDisableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> DisableKinesisStreamingDestination(Dafny.Com.Amazonaws.Dynamodb.Types._IDisableKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.DisableKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S39_DisableKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.DisableKinesisStreamingDestinationResponse sdkResponse =
 this._impl.DisableKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDisableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S40_DisableKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IDisableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IEnableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> EnableKinesisStreamingDestination(Dafny.Com.Amazonaws.Dynamodb.Types._IEnableKinesisStreamingDestinationInput request) {
 Amazon.DynamoDBv2.Model.EnableKinesisStreamingDestinationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S38_EnableKinesisStreamingDestinationInput(request); try {
 Amazon.DynamoDBv2.Model.EnableKinesisStreamingDestinationResponse sdkResponse =
 this._impl.EnableKinesisStreamingDestinationAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IEnableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S39_EnableKinesisStreamingDestinationOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IEnableKinesisStreamingDestinationOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ExecuteStatement(Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteStatementInput request) {
 Amazon.DynamoDBv2.Model.ExecuteStatementRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_ExecuteStatementInput(request); try {
 Amazon.DynamoDBv2.Model.ExecuteStatementResponse sdkResponse =
 this._impl.ExecuteStatementAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_ExecuteStatementOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteStatementOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteTransactionOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ExecuteTransaction(Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteTransactionInput request) {
 Amazon.DynamoDBv2.Model.ExecuteTransactionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_ExecuteTransactionInput(request); try {
 Amazon.DynamoDBv2.Model.ExecuteTransactionResponse sdkResponse =
 this._impl.ExecuteTransactionAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteTransactionOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_ExecuteTransactionOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExecuteTransactionOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IExportTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ExportTableToPointInTime(Dafny.Com.Amazonaws.Dynamodb.Types._IExportTableToPointInTimeInput request) {
 Amazon.DynamoDBv2.Model.ExportTableToPointInTimeRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_ExportTableToPointInTimeInput(request); try {
 Amazon.DynamoDBv2.Model.ExportTableToPointInTimeResponse sdkResponse =
 this._impl.ExportTableToPointInTimeAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExportTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_ExportTableToPointInTimeOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IExportTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> GetItem(Dafny.Com.Amazonaws.Dynamodb.Types._IGetItemInput request) {
 Amazon.DynamoDBv2.Model.GetItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S12_GetItemInput(request); try {
 Amazon.DynamoDBv2.Model.GetItemResponse sdkResponse =
 this._impl.GetItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S13_GetItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IGetItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IImportTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ImportTable(Dafny.Com.Amazonaws.Dynamodb.Types._IImportTableInput request) {
 Amazon.DynamoDBv2.Model.ImportTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ImportTableInput(request); try {
 Amazon.DynamoDBv2.Model.ImportTableResponse sdkResponse =
 this._impl.ImportTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IImportTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ImportTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IImportTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListBackups(Dafny.Com.Amazonaws.Dynamodb.Types._IListBackupsInput request) {
 Amazon.DynamoDBv2.Model.ListBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.ListBackupsResponse sdkResponse =
 this._impl.ListBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListContributorInsights(Dafny.Com.Amazonaws.Dynamodb.Types._IListContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.ListContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_ListContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.ListContributorInsightsResponse sdkResponse =
 this._impl.ListContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_ListContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListExportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListExports(Dafny.Com.Amazonaws.Dynamodb.Types._IListExportsInput request) {
 Amazon.DynamoDBv2.Model.ListExportsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListExportsInput(request); try {
 Amazon.DynamoDBv2.Model.ListExportsResponse sdkResponse =
 this._impl.ListExportsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListExportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListExportsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListExportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListGlobalTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListGlobalTables(Dafny.Com.Amazonaws.Dynamodb.Types._IListGlobalTablesInput request) {
 Amazon.DynamoDBv2.Model.ListGlobalTablesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_ListGlobalTablesInput(request); try {
 Amazon.DynamoDBv2.Model.ListGlobalTablesResponse sdkResponse =
 this._impl.ListGlobalTablesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListGlobalTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_ListGlobalTablesOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListGlobalTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListImportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListImports(Dafny.Com.Amazonaws.Dynamodb.Types._IListImportsInput request) {
 Amazon.DynamoDBv2.Model.ListImportsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListImportsInput(request); try {
 Amazon.DynamoDBv2.Model.ListImportsResponse sdkResponse =
 this._impl.ListImportsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListImportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_ListImportsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListImportsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListTables(Dafny.Com.Amazonaws.Dynamodb.Types._IListTablesInput request) {
 Amazon.DynamoDBv2.Model.ListTablesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_ListTablesInput(request); try {
 Amazon.DynamoDBv2.Model.ListTablesResponse sdkResponse =
 this._impl.ListTablesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_ListTablesOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListTablesOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IListTagsOfResourceOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> ListTagsOfResource(Dafny.Com.Amazonaws.Dynamodb.Types._IListTagsOfResourceInput request) {
 Amazon.DynamoDBv2.Model.ListTagsOfResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_ListTagsOfResourceInput(request); try {
 Amazon.DynamoDBv2.Model.ListTagsOfResourceResponse sdkResponse =
 this._impl.ListTagsOfResourceAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListTagsOfResourceOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_ListTagsOfResourceOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IListTagsOfResourceOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IPutItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> PutItem(Dafny.Com.Amazonaws.Dynamodb.Types._IPutItemInput request) {
 Amazon.DynamoDBv2.Model.PutItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S12_PutItemInput(request); try {
 Amazon.DynamoDBv2.Model.PutItemResponse sdkResponse =
 this._impl.PutItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IPutItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S13_PutItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IPutItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IQueryOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> Query(Dafny.Com.Amazonaws.Dynamodb.Types._IQueryInput request) {
 Amazon.DynamoDBv2.Model.QueryRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S10_QueryInput(request); try {
 Amazon.DynamoDBv2.Model.QueryResponse sdkResponse =
 this._impl.QueryAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IQueryOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S11_QueryOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IQueryOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableFromBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> RestoreTableFromBackup(Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableFromBackupInput request) {
 Amazon.DynamoDBv2.Model.RestoreTableFromBackupRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S27_RestoreTableFromBackupInput(request); try {
 Amazon.DynamoDBv2.Model.RestoreTableFromBackupResponse sdkResponse =
 this._impl.RestoreTableFromBackupAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableFromBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_RestoreTableFromBackupOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableFromBackupOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> RestoreTableToPointInTime(Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableToPointInTimeInput request) {
 Amazon.DynamoDBv2.Model.RestoreTableToPointInTimeRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_RestoreTableToPointInTimeInput(request); try {
 Amazon.DynamoDBv2.Model.RestoreTableToPointInTimeResponse sdkResponse =
 this._impl.RestoreTableToPointInTimeAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_RestoreTableToPointInTimeOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IRestoreTableToPointInTimeOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IScanOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> Scan(Dafny.Com.Amazonaws.Dynamodb.Types._IScanInput request) {
 Amazon.DynamoDBv2.Model.ScanRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_ScanInput(request); try {
 Amazon.DynamoDBv2.Model.ScanResponse sdkResponse =
 this._impl.ScanAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IScanOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S10_ScanOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IScanOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError> TagResource(Dafny.Com.Amazonaws.Dynamodb.Types._ITagResourceInput request) {
 Amazon.DynamoDBv2.Model.TagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_TagResourceInput(request); try {

 this._impl.TagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactGetItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> TransactGetItems(Dafny.Com.Amazonaws.Dynamodb.Types._ITransactGetItemsInput request) {
 Amazon.DynamoDBv2.Model.TransactGetItemsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_TransactGetItemsInput(request); try {
 Amazon.DynamoDBv2.Model.TransactGetItemsResponse sdkResponse =
 this._impl.TransactGetItemsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactGetItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_TransactGetItemsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactGetItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactWriteItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> TransactWriteItems(Dafny.Com.Amazonaws.Dynamodb.Types._ITransactWriteItemsInput request) {
 Amazon.DynamoDBv2.Model.TransactWriteItemsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_TransactWriteItemsInput(request); try {
 Amazon.DynamoDBv2.Model.TransactWriteItemsResponse sdkResponse =
 this._impl.TransactWriteItemsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactWriteItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S24_TransactWriteItemsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._ITransactWriteItemsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UntagResource(Dafny.Com.Amazonaws.Dynamodb.Types._IUntagResourceInput request) {
 Amazon.DynamoDBv2.Model.UntagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S18_UntagResourceInput(request); try {

 this._impl.UntagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateContinuousBackups(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContinuousBackupsInput request) {
 Amazon.DynamoDBv2.Model.UpdateContinuousBackupsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S28_UpdateContinuousBackupsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateContinuousBackupsResponse sdkResponse =
 this._impl.UpdateContinuousBackupsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S29_UpdateContinuousBackupsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContinuousBackupsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateContributorInsights(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContributorInsightsInput request) {
 Amazon.DynamoDBv2.Model.UpdateContributorInsightsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_UpdateContributorInsightsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateContributorInsightsResponse sdkResponse =
 this._impl.UpdateContributorInsightsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_UpdateContributorInsightsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateContributorInsightsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateGlobalTable(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableInput request) {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_UpdateGlobalTableInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableResponse sdkResponse =
 this._impl.UpdateGlobalTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S23_UpdateGlobalTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateGlobalTableSettings(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableSettingsInput request) {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableSettingsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S30_UpdateGlobalTableSettingsInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateGlobalTableSettingsResponse sdkResponse =
 this._impl.UpdateGlobalTableSettingsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S31_UpdateGlobalTableSettingsOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateGlobalTableSettingsOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateItem(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateItemInput request) {
 Amazon.DynamoDBv2.Model.UpdateItemRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S15_UpdateItemInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateItemResponse sdkResponse =
 this._impl.UpdateItemAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_UpdateItemOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateItemOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateTable(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableInput request) {
 Amazon.DynamoDBv2.Model.UpdateTableRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S16_UpdateTableInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTableResponse sdkResponse =
 this._impl.UpdateTableAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S17_UpdateTableOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateTableReplicaAutoScaling(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableReplicaAutoScalingInput request) {
 Amazon.DynamoDBv2.Model.UpdateTableReplicaAutoScalingRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S34_UpdateTableReplicaAutoScalingInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTableReplicaAutoScalingResponse sdkResponse =
 this._impl.UpdateTableReplicaAutoScalingAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S35_UpdateTableReplicaAutoScalingOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTableReplicaAutoScalingOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError> UpdateTimeToLive(Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTimeToLiveInput request) {
 Amazon.DynamoDBv2.Model.UpdateTimeToLiveRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S21_UpdateTimeToLiveInput(request); try {
 Amazon.DynamoDBv2.Model.UpdateTimeToLiveResponse sdkResponse =
 this._impl.UpdateTimeToLiveAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S22_UpdateTimeToLiveOutput(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.DynamoDBv2.AmazonDynamoDBException ex) {
    return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Dynamodb.Types._IUpdateTimeToLiveOutput, Dafny.Com.Amazonaws.Dynamodb.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
}
}
