// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// ReSharper disable RedundantUsingDirective
// ReSharper disable RedundantNameQualifier
// ReSharper disable SuggestVarOrType_SimpleTypes
 using System;
 using _System;
 using Wrappers_Compile;

 namespace AWS.Cryptography.MaterialProviders {
 internal class NativeWrapper_BranchKeyIdSupplier : software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier 
 {
 internal readonly BranchKeyIdSupplierBase _impl;
 public NativeWrapper_BranchKeyIdSupplier(BranchKeyIdSupplierBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetBranchKeyId(software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._GetBranchKeyId is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.GetBranchKeyIdInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_GetBranchKeyIdInput(input);
 try {
 AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput nativeOutput = _impl.GetBranchKeyId(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._GetBranchKeyId returned null, should be {typeof(AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S20_GetBranchKeyIdOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetBranchKeyId_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
}
}
