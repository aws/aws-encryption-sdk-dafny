// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.EncryptionSDK;
 using software.amazon.cryptography.encryptionsdk.internaldafny.types; namespace AWS.Cryptography.EncryptionSDK {
 public class ESDK {
 private readonly software.amazon.cryptography.encryptionsdk.internaldafny.types.IAwsEncryptionSdkClient _impl;
 public ESDK(software.amazon.cryptography.encryptionsdk.internaldafny.types.IAwsEncryptionSdkClient impl) {
    this._impl = impl;
}
 public software.amazon.cryptography.encryptionsdk.internaldafny.types.IAwsEncryptionSdkClient impl() {
    return this._impl;
}
 public ESDK(AWS.Cryptography.EncryptionSDK.AwsEncryptionSdkConfig input)
 {
 software.amazon.cryptography.encryptionsdk.internaldafny.types._IAwsEncryptionSdkConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N13_encryptionSdk__S22_AwsEncryptionSdkConfig(input);
 var result = software.amazon.cryptography.encryptionsdk.internaldafny.__default.ESDK(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.EncryptionSDK.EncryptOutput Encrypt(AWS.Cryptography.EncryptionSDK.EncryptInput input) {
 software.amazon.cryptography.encryptionsdk.internaldafny.types._IEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N13_encryptionSdk__S12_EncryptInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.encryptionsdk.internaldafny.types._IEncryptOutput, software.amazon.cryptography.encryptionsdk.internaldafny.types._IError> result = _impl.Encrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N13_encryptionSdk__S13_EncryptOutput(result.dtor_value);
}
 public AWS.Cryptography.EncryptionSDK.DecryptOutput Decrypt(AWS.Cryptography.EncryptionSDK.DecryptInput input) {
 software.amazon.cryptography.encryptionsdk.internaldafny.types._IDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N13_encryptionSdk__S12_DecryptInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.encryptionsdk.internaldafny.types._IDecryptOutput, software.amazon.cryptography.encryptionsdk.internaldafny.types._IError> result = _impl.Decrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N13_encryptionSdk__S13_DecryptOutput(result.dtor_value);
}
}
}
