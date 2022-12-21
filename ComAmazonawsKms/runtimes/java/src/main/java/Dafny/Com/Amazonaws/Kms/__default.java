// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package Dafny.Com.Amazonaws.Kms;

import com.amazonaws.regions.DefaultAwsRegionProviderChain;
import com.amazonaws.services.kms.AWSKMS;
import com.amazonaws.services.kms.AWSKMSClient;
import com.amazonaws.services.kms.AWSKMSClientBuilder;

import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import dafny.DafnySequence;


import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends Dafny.Com.Amazonaws.Kms._ExternBase___default{
    public static Result<IKeyManagementServiceClient, Error> KMSClient() {
        try {
            // TODO This assumes that the SDK will continue to default to using the DefaulAwsRegionProviderChain.
            // If this is ever not true in the future, then the behavior here may be surprising.
            // Determine the likelihood/impact of this changing, and if this is the correct tradeoff to make.
            String region = new DefaultAwsRegionProviderChain().getRegion();

            AWSKMS client = AWSKMSClientBuilder.standard()
                                               .withRegion(region)
                                               .build();
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
}
