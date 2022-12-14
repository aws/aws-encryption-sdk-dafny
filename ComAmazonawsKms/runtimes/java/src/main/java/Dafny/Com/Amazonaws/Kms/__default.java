// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package Dafny.Com.Amazonaws.Kms;

import com.amazonaws.services.kms.AWSKMS;
import com.amazonaws.services.kms.AWSKMSClient;

import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import dafny.DafnySequence;

// TODO: restore next two lines once software.amazon.dafny.conversion is added
//import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
//import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default extends Dafny.Com.Amazonaws.Kms._ExternBase___default{
    public static Result<IKeyManagementServiceClient, Error> KMSClient() {
        return Result.create_Failure(null);
    }

    public static Wrappers_Compile.Option<Boolean> RegionMatch(
            final IKeyManagementServiceClient client,
            final DafnySequence<? extends Character> region
    ) {
        // TODO: restore next line once software.amazon.dafny.conversion is added
        //String regionStr = String(region);
        // TODO: restore next two lines once Shim is generated and commited
        // String actualRegion = ((Shim) client).region();
        // return Option.create_Some(regionStr.equals(actualRegion));
        return Option.create_None();
    }
}
