// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.cryptography.services.dynamodb.internaldafny;

import software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.Error;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import software.amazon.awssdk.auth.credentials.ProfileCredentialsProvider;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import dafny.DafnySequence;


import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends software.amazon.cryptography.services.dynamodb.internaldafny._ExternBase___default{
    public static Result<IDynamoDBClient, Error> DynamoDBClient() {
        try {
            Region region = new DefaultAwsRegionProviderChain().getRegion();
            final DynamoDbClient ddbClient = DynamoDbClient.builder()
                    .region(region)
                    .build();

            IDynamoDBClient shim = new Shim(ddbClient, region.toString());
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_InternalServerError(
                    Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

    public static Result<IDynamoDBClient, Error> DDBClientForRegion(
            final DafnySequence<? extends Character> region
    ) {
        try {
            final String regionString = new String((char[]) region.toArray().unwrap());
            final DynamoDbClient ddbClient = DynamoDbClient.builder()
                    .region(Region.of(regionString))
                    .build();

            IDynamoDBClient shim = new Shim(ddbClient, regionString);
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_InternalServerError(
                    Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

}
