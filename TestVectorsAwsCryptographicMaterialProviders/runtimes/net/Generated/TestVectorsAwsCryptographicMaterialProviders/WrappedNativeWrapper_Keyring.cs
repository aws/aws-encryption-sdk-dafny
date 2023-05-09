// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// ReSharper disable RedundantUsingDirective
// ReSharper disable RedundantNameQualifier
// ReSharper disable SuggestVarOrType_SimpleTypes
 using System;
 using _System;
 using Wrappers_Compile;

 namespace AWS.Cryptography.MaterialProviders.Wrapped {
 internal class WrappedNativeWrapper_Keyring : software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring 
 {
 internal readonly KeyringBase _impl;
 public WrappedNativeWrapper_Keyring(KeyringBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.OnEncryptOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._OnEncrypt is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.OnEncryptInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S14_OnEncryptInput(input);
 try {
 AWS.Cryptography.MaterialProviders.OnEncryptOutput nativeOutput = _impl.OnEncrypt(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._OnEncrypt returned null, should be {typeof(AWS.Cryptography.MaterialProviders.OnEncryptOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S15_OnEncryptOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.OnDecryptOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._OnDecrypt is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.OnDecryptInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S14_OnDecryptInput(input);
 try {
 AWS.Cryptography.MaterialProviders.OnDecryptOutput nativeOutput = _impl.OnDecrypt(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._OnDecrypt returned null, should be {typeof(AWS.Cryptography.MaterialProviders.OnDecryptOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S15_OnDecryptOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
}
}
