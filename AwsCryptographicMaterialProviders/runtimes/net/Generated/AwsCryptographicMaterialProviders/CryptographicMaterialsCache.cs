// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProviders;
 using software.amazon.cryptography.materialproviders.internaldafny.types; namespace AWS.Cryptography.MaterialProviders {
 internal class CryptographicMaterialsCache : CryptographicMaterialsCacheBase {
 internal readonly software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache _impl;
 internal CryptographicMaterialsCache(software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache impl) { this._impl = impl; }
 protected override void _PutCacheEntry(AWS.Cryptography.MaterialProviders.PutCacheEntryInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_PutCacheEntryInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = this._impl.PutCacheEntry(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 protected override void _UpdaterUsageMetadata(AWS.Cryptography.MaterialProviders.UpdaterUsageMetadataInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IUpdaterUsageMetadataInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S25_UpdaterUsageMetadataInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = this._impl.UpdaterUsageMetadata(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 protected override AWS.Cryptography.MaterialProviders.GetCacheEntryOutput _GetCacheEntry(AWS.Cryptography.MaterialProviders.GetCacheEntryInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_GetCacheEntryInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = this._impl.GetCacheEntry(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_GetCacheEntryOutput(result.dtor_value);
}
 protected override void _DeleteCacheEntry(AWS.Cryptography.MaterialProviders.DeleteCacheEntryInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S21_DeleteCacheEntryInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = this._impl.DeleteCacheEntry(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
}
}
