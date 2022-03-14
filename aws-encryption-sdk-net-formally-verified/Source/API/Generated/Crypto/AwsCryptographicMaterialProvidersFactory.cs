// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public static class AwsCryptographicMaterialProvidersFactory
    {
        static Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersFactory.AwsCryptographicMaterialProvidersFactory
            _impl =
                new Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersFactory.
                    AwsCryptographicMaterialProvidersFactory();

        public static Aws.Encryption.Core.IAwsCryptographicMaterialProviders CreateDefaultAwsCryptographicMaterialProviders()
        {
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProviders,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                _impl.CreateDefaultAwsCryptographicMaterialProviders();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                result.dtor_value);
        }
    }
}
