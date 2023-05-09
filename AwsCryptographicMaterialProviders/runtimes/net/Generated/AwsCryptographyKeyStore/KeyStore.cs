// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.KeyStore;
 using software.amazon.cryptography.keystore.internaldafny.types; namespace AWS.Cryptography.KeyStore {
 public class KeyStore {
 private readonly software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient _impl;
 public KeyStore(software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient impl) {
    this._impl = impl;
}
 public software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient impl() {
    return this._impl;
}
 public KeyStore(AWS.Cryptography.KeyStore.KeyStoreConfig input)
 {
 software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig(input);
 var result = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput GetKeyStoreInfo() {

 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.GetKeyStoreInfo();
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.CreateKeyStoreOutput CreateKeyStore(AWS.Cryptography.KeyStore.CreateKeyStoreInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.CreateKeyStore(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.CreateKeyOutput CreateKey() {

 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.CreateKey();
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput(result.dtor_value);
}
 public void VersionKey(AWS.Cryptography.KeyStore.VersionKeyInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.VersionKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput GetActiveBranchKey(AWS.Cryptography.KeyStore.GetActiveBranchKeyInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.GetActiveBranchKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput GetBranchKeyVersion(AWS.Cryptography.KeyStore.GetBranchKeyVersionInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.GetBranchKeyVersion(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.GetBeaconKeyOutput GetBeaconKey(AWS.Cryptography.KeyStore.GetBeaconKeyInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.GetBeaconKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput(result.dtor_value);
}
 public void BranchKeyStatusResolution(AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput input) {
 software.amazon.cryptography.keystore.internaldafny.types._IBranchKeyStatusResolutionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.keystore.internaldafny.types._IError> result = _impl.BranchKeyStatusResolution(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
}
}
