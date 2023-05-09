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
 internal class NativeWrapper_CryptographicMaterialsManager : software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager 
 {
 internal readonly CryptographicMaterialsManagerBase _impl;
 public NativeWrapper_CryptographicMaterialsManager(CryptographicMaterialsManagerBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._GetEncryptionMaterials is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_GetEncryptionMaterialsInput(input);
 try {
 AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput nativeOutput = _impl.GetEncryptionMaterials(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._GetEncryptionMaterials returned null, should be {typeof(AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S28_GetEncryptionMaterialsOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetEncryptionMaterials_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DecryptMaterials(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._DecryptMaterials is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.DecryptMaterialsInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S21_DecryptMaterialsInput(input);
 try {
 AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput nativeOutput = _impl.DecryptMaterials(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._DecryptMaterials returned null, should be {typeof(AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S22_DecryptMaterialsOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DecryptMaterials_k(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
}
}
