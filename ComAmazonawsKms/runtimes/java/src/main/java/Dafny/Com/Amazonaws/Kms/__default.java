// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Extern code for AWS SDK for Java V2
package Dafny.Com.Amazonaws.Kms;

import dafny.DafnySequence;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.AwsRegionProviderChain;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.KmsClientBuilder;

import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;

import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends Dafny.Com.Amazonaws.Kms._ExternBase___default{
    public static Result<IKeyManagementServiceClient, Error> KMSClient() {
        try {
            KmsClientBuilder builder = KmsClient.builder();
            AwsRegionProviderChain regionProvider = DefaultAwsRegionProviderChain.builder().build();
            String region = regionProvider.getRegion().toString();
            KmsClient client = builder.build();
            IKeyManagementServiceClient shim = new Shim(client, region);
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_KMSInternalException(
              Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

    public static Result<IKeyManagementServiceClient, Error> KMSClient(final String region) {
        try {
            KmsClientBuilder builder = KmsClient.builder();
            KmsClient client = builder.region(Region.of(region)).build();
            IKeyManagementServiceClient shim = new Shim(client, region);
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_KMSInternalException(
              Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

    public static Wrappers_Compile.Option<Boolean> RegionMatch(
      final IKeyManagementServiceClient client,
      final DafnySequence<? extends Character> region
    ) {
        // We should never be passing anything other than Shim as the 'client'.
        // If this cast fails, that indicates that there is something wrong withß
        // our code generation.
        Shim shim = (Shim) client;

        // If the client was created externally we
        // have no way to determine what region it is
        // configured with.
        if (shim.region() == null) {
            return Option.create_None();
        }

        // Otherwise we kept record of the region
        // when we created the client.
        String shimRegion = shim.region();
        String regionStr = String(region);
        return Option.create_Some(regionStr.equals(shimRegion));
    }
}