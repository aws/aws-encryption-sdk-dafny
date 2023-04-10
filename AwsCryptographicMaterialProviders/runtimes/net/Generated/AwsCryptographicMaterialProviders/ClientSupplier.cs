// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProviders;
 using Dafny.Aws.Cryptography.MaterialProviders.Types; namespace AWS.Cryptography.MaterialProviders {
 internal class ClientSupplier : ClientSupplierBase {
 internal readonly Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier _impl;
 internal ClientSupplier(Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier impl) { this._impl = impl; }
 protected override Amazon.KeyManagementService.IAmazonKeyManagementService _GetClient(AWS.Cryptography.MaterialProviders.GetClientInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IGetClientInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S14_GetClientInput(input);
 Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.Types.IKMSClient, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = this._impl.GetClient(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S15_GetClientOutput(result.dtor_value);
}
}
}
