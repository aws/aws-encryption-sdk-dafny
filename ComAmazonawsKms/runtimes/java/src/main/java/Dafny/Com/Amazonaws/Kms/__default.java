// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Extern code for AWS SDK for Java V2
package Dafny.Com.Amazonaws.Kms;

import dafny.DafnySequence;
import software.amazon.awssdk.core.client.config.ClientOverrideConfiguration;
import software.amazon.awssdk.core.client.config.SdkAdvancedClientOption;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.AwsRegionProviderChain;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.KmsClientBuilder;

import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKMSClient;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;

import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends Dafny.Com.Amazonaws.Kms._ExternBase___default{
    public static Result<IKMSClient, Error> KMSClient() {
        try {
            final KmsClientBuilder builder = KmsClient.builder();
            final AwsRegionProviderChain regionProvider = DefaultAwsRegionProviderChain.builder().build();
            final String region = regionProvider.getRegion().toString();
            final KmsClient client = builder
              .overrideConfiguration(
                ClientOverrideConfiguration
                  .builder()
                  .putAdvancedOption(SdkAdvancedClientOption.USER_AGENT_SUFFIX, UserAgentSuffix())
                  .build()
              )
              .build();
            final IKMSClient shim = new Shim(client, region);
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_KMSInternalException(
              Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

    public static Result<IKMSClient, Error> KMSClientForRegion(
        final DafnySequence<? extends Character> region
    ) {
        try {
            final String regionString = new String((char[]) region.toArray().unwrap());
            final KmsClientBuilder builder = KmsClient.builder();
            final KmsClient client = builder
              .region(Region.of(regionString))
              .overrideConfiguration(
                ClientOverrideConfiguration
                  .builder()
                  .putAdvancedOption(SdkAdvancedClientOption.USER_AGENT_SUFFIX, UserAgentSuffix())
                  .build()
              )
              .build();
            final IKMSClient shim = new Shim(client, regionString);
            return Result.create_Success(shim);
        } catch (Exception e) {
            Error dafny_error = Error.create_KMSInternalException(
              Option.create_Some(CharacterSequence(e.getMessage())));
            return Result.create_Failure(dafny_error);
        }
    }

    public static Wrappers_Compile.Option<Boolean> RegionMatch(
      final IKMSClient client,
      final DafnySequence<? extends Character> region
    ) {
        // We should never be passing anything other than Shim as the 'client'.
        // If this cast fails, that indicates that there is something wrong with
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

    private static String UserAgentSuffix()
    {
        final DafnySequence<? extends Character> runtime = software.amazon.dafny.conversion.ToDafny.Simple
          .CharacterSequence("Java");
        return new String(
          (char[]) DafnyUserAgentSuffix(runtime).toArray().unwrap()
        );
    }
}