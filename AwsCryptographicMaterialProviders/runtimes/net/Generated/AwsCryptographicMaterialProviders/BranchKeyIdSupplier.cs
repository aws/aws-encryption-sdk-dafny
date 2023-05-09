// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProviders;
 using software.amazon.cryptography.materialproviders.internaldafny.types; namespace AWS.Cryptography.MaterialProviders {
 internal class BranchKeyIdSupplier : BranchKeyIdSupplierBase {
 internal readonly software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier _impl;
 internal BranchKeyIdSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier impl) { this._impl = impl; }
 protected override AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput _GetBranchKeyId(AWS.Cryptography.MaterialProviders.GetBranchKeyIdInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_GetBranchKeyIdInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = this._impl.GetBranchKeyId(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S20_GetBranchKeyIdOutput(result.dtor_value);
}
}
}
