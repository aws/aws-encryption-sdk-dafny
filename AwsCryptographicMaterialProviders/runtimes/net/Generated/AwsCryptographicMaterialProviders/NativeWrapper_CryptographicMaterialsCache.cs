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
 internal class NativeWrapper_CryptographicMaterialsCache : software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache 
 {
 internal readonly CryptographicMaterialsCacheBase _impl;
 public NativeWrapper_CryptographicMaterialsCache(CryptographicMaterialsCacheBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> PutCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput input)
 {

 AWS.Cryptography.MaterialProviders.PutCacheEntryInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_PutCacheEntryInput(input);
 try {
  _impl.PutCacheEntry(nativeInput);
 
 
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(Tuple0.create());
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> PutCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> UpdaterUsageMetadata(software.amazon.cryptography.materialproviders.internaldafny.types._IUpdaterUsageMetadataInput input)
 {

 AWS.Cryptography.MaterialProviders.UpdaterUsageMetadataInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S25_UpdaterUsageMetadataInput(input);
 try {
  _impl.UpdaterUsageMetadata(nativeInput);
 
 
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(Tuple0.create());
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> UpdaterUsageMetadata_k(software.amazon.cryptography.materialproviders.internaldafny.types._IUpdaterUsageMetadataInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput input)
 {
 void validateOutput(AWS.Cryptography.MaterialProviders.GetCacheEntryOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._GetCacheEntry is invalid. {e.Message}";
 throw new AwsCryptographicMaterialProvidersException(message);
}
}
 AWS.Cryptography.MaterialProviders.GetCacheEntryInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_GetCacheEntryInput(input);
 try {
 AWS.Cryptography.MaterialProviders.GetCacheEntryOutput nativeOutput = _impl.GetCacheEntry(nativeInput);
 _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._GetCacheEntry returned null, should be {typeof(AWS.Cryptography.MaterialProviders.GetCacheEntryOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_GetCacheEntryOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DeleteCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput input)
 {

 AWS.Cryptography.MaterialProviders.DeleteCacheEntryInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S21_DeleteCacheEntryInput(input);
 try {
  _impl.DeleteCacheEntry(nativeInput);
 
 
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(Tuple0.create());
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DeleteCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput input)
 {
 throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
}
}
}
