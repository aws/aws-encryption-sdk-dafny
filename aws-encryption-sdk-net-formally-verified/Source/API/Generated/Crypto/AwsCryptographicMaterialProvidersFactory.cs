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
    public static class AwsCryptographicMaterialProvidersFactory
    {
        static Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersFactory.AwsCryptographicMaterialProvidersFactory
            _impl =
                new Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersFactory.
                    AwsCryptographicMaterialProvidersFactory();

        public static Aws.Crypto.IAwsCryptographicMaterialProviders CreateDefaultAwsCryptographicMaterialProviders()
        {
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IAwsCryptographicMaterialProviders,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                _impl.CreateDefaultAwsCryptographicMaterialProviders();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S42_AwsCryptographicMaterialProvidersReference(
                result.dtor_value);
        }
    }
}
