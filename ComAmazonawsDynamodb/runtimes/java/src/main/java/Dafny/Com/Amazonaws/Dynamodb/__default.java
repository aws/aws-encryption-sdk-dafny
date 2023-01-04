// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package Dafny.Com.Amazonaws.Dynamodb;

import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDB__20120810Client;
import Dafny.Com.Amazonaws.Dynamodb.Types.Error;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import software.amazon.awssdk.auth.credentials.ProfileCredentialsProvider;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import dafny.DafnySequence;


import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends Dafny.Com.Amazonaws.Dynamodb._ExternBase___default{
    public static Result<IDynamoDB__20120810Client, Error> DynamoDBClient() {
        try {
            ProfileCredentialsProvider credentialsProvider = ProfileCredentialsProvider.create();
            Region region = new DefaultAwsRegionProviderChain().getRegion();
            final DynamoDbClient ddbClient = DynamoDbClient.builder()
                    .credentialsProvider(credentialsProvider)
                    .region(region)
                    .build();

            IDynamoDB__20120810Client shim = new Shim(ddbClient, region.toString());
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_InternalServerError(
                    Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }
}
