// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.KeyStore;
 using Dafny.Aws.Cryptography.KeyStore.Types; namespace AWS.Cryptography.KeyStore {
 public class KeyStore {
 private readonly Dafny.Aws.Cryptography.KeyStore.Types.IKeyStoreClient _impl;
 public KeyStore(Dafny.Aws.Cryptography.KeyStore.Types.IKeyStoreClient impl) {
    this._impl = impl;
}
 public Dafny.Aws.Cryptography.KeyStore.Types.IKeyStoreClient impl() {
    return this._impl;
}
 public KeyStore(AWS.Cryptography.KeyStore.KeyStoreConfig input)
 {
 Dafny.Aws.Cryptography.KeyStore.Types._IKeyStoreConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig(input);
 var result = Dafny.Aws.Cryptography.KeyStore.__default.KeyStore(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.KeyStore.CreateKeyStoreOutput CreateKeyStore(AWS.Cryptography.KeyStore.CreateKeyStoreInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreOutput, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.CreateKeyStore(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.CreateKeyOutput CreateKey() {

 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyOutput, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.CreateKey();
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput(result.dtor_value);
}
 public void VersionKey(AWS.Cryptography.KeyStore.VersionKeyInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._IVersionKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.VersionKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput GetActiveBranchKey(AWS.Cryptography.KeyStore.GetActiveBranchKeyInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyOutput, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.GetActiveBranchKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput GetBranchKeyVersion(AWS.Cryptography.KeyStore.GetBranchKeyVersionInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionOutput, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.GetBranchKeyVersion(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput(result.dtor_value);
}
 public AWS.Cryptography.KeyStore.GetBeaconKeyOutput GetBeaconKey(AWS.Cryptography.KeyStore.GetBeaconKeyInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyOutput, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.GetBeaconKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput(result.dtor_value);
}
 public void BranchKeyStatusResolution(AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput input) {
 Dafny.Aws.Cryptography.KeyStore.Types._IBranchKeyStatusResolutionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.KeyStore.Types._IError> result = _impl.BranchKeyStatusResolution(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
}
}
