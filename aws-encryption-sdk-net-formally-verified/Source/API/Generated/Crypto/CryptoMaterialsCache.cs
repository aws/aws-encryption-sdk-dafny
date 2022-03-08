// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using System.IO;
 using System.Collections.Generic;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 internal class CryptoMaterialsCache : CryptoMaterialsCacheBase {
 internal Dafny.Aws.Crypto.ICryptoMaterialsCache _impl { get; }
 internal CryptoMaterialsCache(Dafny.Aws.Crypto.ICryptoMaterialsCache impl) { this._impl = impl; }
 protected override Aws.Crypto.DeleteEntryOutput _DeleteEntry(Aws.Crypto.DeleteEntryInput input) {
 Dafny.Aws.Crypto._IDeleteEntryInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Crypto._IDeleteEntryOutput, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result = this._impl.DeleteEntry(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S17_DeleteEntryOutput(result.dtor_value);
}
 protected override Aws.Crypto.PutEntryForEncryptOutput _PutEntryForEncrypt(Aws.Crypto.PutEntryForEncryptInput input) {
 Dafny.Aws.Crypto._IPutEntryForEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Crypto._IPutEntryForEncryptOutput, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result = this._impl.PutEntryForEncrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForEncryptOutput(result.dtor_value);
}
 protected override Aws.Crypto.GetEntryForDecryptOutput _GetEntryForDecrypt(Aws.Crypto.GetEntryForDecryptInput input) {
 Dafny.Aws.Crypto._IGetEntryForDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Crypto._IGetEntryForDecryptOutput, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result = this._impl.GetEntryForDecrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput(result.dtor_value);
}
 protected override Aws.Crypto.GetEntryForEncryptOutput _GetEntryForEncrypt(Aws.Crypto.GetEntryForEncryptInput input) {
 Dafny.Aws.Crypto._IGetEntryForEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Crypto._IGetEntryForEncryptOutput, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result = this._impl.GetEntryForEncrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput(result.dtor_value);
}
 protected override Aws.Crypto.PutEntryForDecryptOutput _PutEntryForDecrypt(Aws.Crypto.PutEntryForDecryptInput input) {
 Dafny.Aws.Crypto._IPutEntryForDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Crypto._IPutEntryForDecryptOutput, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result = this._impl.PutEntryForDecrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForDecryptOutput(result.dtor_value);
}
}
}
