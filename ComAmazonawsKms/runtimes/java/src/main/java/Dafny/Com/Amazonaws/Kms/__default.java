// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package Dafny.Com.Amazonaws.Kms;

import com.amazonaws.services.kms.AWSKMS;
import com.amazonaws.services.kms.AWSKMSClient;

import Dafny.Com.Amazonaws.Kms.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;

public class __default extends Dafny.Com.Amazonaws.Kms._ExternBase___default{
    public static Result<IKeyManagementServiceClient, Error> KMSClient() {
        return Result.create_Failure(null);
    }
}
