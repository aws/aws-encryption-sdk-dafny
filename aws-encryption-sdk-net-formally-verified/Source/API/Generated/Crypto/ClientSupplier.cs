// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.EncryptionSdk;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    internal class ClientSupplier : ClientSupplierBase
    {
        internal Dafny.Aws.EncryptionSdk.Core.IClientSupplier _impl { get; }

        internal ClientSupplier(Dafny.Aws.EncryptionSdk.Core.IClientSupplier impl)
        {
            this._impl = impl;
        }

        protected override Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(
            Aws.EncryptionSdk.Core.GetClientInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._IGetClientInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(input);
            Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.GetClient(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput(result.dtor_value);
        }
    }
}
