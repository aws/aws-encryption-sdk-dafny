// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public static class AwsCryptographicMaterialProvidersFactory
    {
        static Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersFactory.
            AwsCryptographicMaterialProvidersFactory _impl =
                new Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersFactory.
                    AwsCryptographicMaterialProvidersFactory();

        public static Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders
            CreateDefaultAwsCryptographicMaterialProviders()
        {
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                _impl.CreateDefaultAwsCryptographicMaterialProviders();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion
                .FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                    result.dtor_value);
        }
    }
}
