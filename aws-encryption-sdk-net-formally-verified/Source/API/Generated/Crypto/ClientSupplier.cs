// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using System.IO;
 using System.Collections.Generic;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 internal class ClientSupplier : ClientSupplierBase {
 internal Dafny.Aws.Crypto.IClientSupplier _impl { get; }
 internal ClientSupplier(Dafny.Aws.Crypto.IClientSupplier impl) { this._impl = impl; }
 protected override Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(Aws.Crypto.GetClientInput input) {
 Dafny.Aws.Crypto._IGetClientInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S14_GetClientInput(input);
 Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result = this._impl.GetClient(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S15_GetClientOutput(result.dtor_value);
}
}
}
