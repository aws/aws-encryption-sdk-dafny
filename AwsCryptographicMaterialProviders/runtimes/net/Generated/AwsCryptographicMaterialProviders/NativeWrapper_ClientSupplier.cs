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
 internal class NativeWrapper_ClientSupplier : software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier 
 {
 internal readonly ClientSupplierBase _impl;
 public NativeWrapper_ClientSupplier(ClientSupplierBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetClient(software.amazon.cryptography.materialproviders.internaldafny.types._IGetClientInput input)
 {

 AWS.Cryptography.MaterialProviders.GetClientInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S14_GetClientInput(input);
 try {
 Amazon.KeyManagementService.IAmazonKeyManagementService nativeOutput = _impl.GetClient(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._GetClient returned null, should be {typeof(Amazon.KeyManagementService.IAmazonKeyManagementService)}");
 
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S15_GetClientOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetClient_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetClientInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
}
}
