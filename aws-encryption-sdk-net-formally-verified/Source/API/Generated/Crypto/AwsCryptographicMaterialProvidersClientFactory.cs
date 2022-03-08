// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public static class
        AwsCryptographicMaterialProvidersClientFactory
    {
        public static Aws.Crypto.IAwsCryptographicMaterialProvidersClient
            MakeAwsCryptographicMaterialProvidersClient(Aws.Crypto.AwsCryptographicMaterialProvidersClientConfig input)
        {
            Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientFactory.
                AwsCryptographicMaterialProvidersClientFactory impl =
                    new Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientFactory.
                        AwsCryptographicMaterialProvidersClientFactory();
            Dafny.Aws.Crypto._IAwsCryptographicMaterialProvidersClientConfig internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S45_AwsCryptographicMaterialProvidersClientConfig(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClient,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientException> result =
                impl.MakeAwsCryptographicMaterialProvidersClient(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientReference(
                result.dtor_value);
        }
    }
}
