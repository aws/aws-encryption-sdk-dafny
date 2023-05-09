// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProviders;
 using software.amazon.cryptography.materialproviders.internaldafny.types; namespace AWS.Cryptography.MaterialProviders {
 public class MaterialProviders {
 private readonly software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _impl;
 public MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient impl) {
    this._impl = impl;
}
 public software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient impl() {
    return this._impl;
}
 public MaterialProviders(AWS.Cryptography.MaterialProviders.MaterialProvidersConfig input)
 {
 software.amazon.cryptography.materialproviders.internaldafny.types._IMaterialProvidersConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_MaterialProvidersConfig(input);
 var result = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateAwsKmsKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsDiscoveryKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsDiscoveryKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateAwsKmsDiscoveryKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsDiscoveryKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMultiKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S29_CreateAwsKmsMultiKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsDiscoveryMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryMultiKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsMrkKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsMrkKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkMultiKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateAwsKmsMrkMultiKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsMrkMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkDiscoveryKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkDiscoveryKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsMrkDiscoveryKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsMrkDiscoveryKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkDiscoveryMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsMrkDiscoveryMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsHierarchicalKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsHierarchicalKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsHierarchicalKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsHierarchicalKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsHierarchicalKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateMultiKeyring(AWS.Cryptography.MaterialProviders.CreateMultiKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_CreateMultiKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateRawAesKeyring(AWS.Cryptography.MaterialProviders.CreateRawAesKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawAesKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawAesKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateRawAesKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateRawRsaKeyring(AWS.Cryptography.MaterialProviders.CreateRawRsaKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawRsaKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawRsaKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateRawRsaKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsRsaKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsRsaKeyringInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsRsaKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsRsaKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateAwsKmsRsaKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(AWS.Cryptography.MaterialProviders.CreateDefaultCryptographicMaterialsManagerInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateDefaultCryptographicMaterialsManagerInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateDefaultCryptographicMaterialsManager(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateCryptographicMaterialsManagerOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager CreateExpectedEncryptionContextCMM(AWS.Cryptography.MaterialProviders.CreateExpectedEncryptionContextCMMInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateExpectedEncryptionContextCMMInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_CreateExpectedEncryptionContextCMMInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateExpectedEncryptionContextCMM(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S40_CreateExpectedEncryptionContextCMMOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsCache CreateCryptographicMaterialsCache(AWS.Cryptography.MaterialProviders.CreateCryptographicMaterialsCacheInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateCryptographicMaterialsCacheInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateCryptographicMaterialsCacheInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateCryptographicMaterialsCache(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_CreateCryptographicMaterialsCacheOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IClientSupplier CreateDefaultClientSupplier(AWS.Cryptography.MaterialProviders.CreateDefaultClientSupplierInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._ICreateDefaultClientSupplierInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateDefaultClientSupplierInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.CreateDefaultClientSupplier(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateDefaultClientSupplierOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials InitializeEncryptionMaterials(AWS.Cryptography.MaterialProviders.InitializeEncryptionMaterialsInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IInitializeEncryptionMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeEncryptionMaterialsInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.InitializeEncryptionMaterials(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials InitializeDecryptionMaterials(AWS.Cryptography.MaterialProviders.InitializeDecryptionMaterialsInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IInitializeDecryptionMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeDecryptionMaterialsInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.InitializeDecryptionMaterials(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(result.dtor_value);
}
 public void ValidEncryptionMaterialsTransition(AWS.Cryptography.MaterialProviders.ValidEncryptionMaterialsTransitionInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IValidEncryptionMaterialsTransitionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidEncryptionMaterialsTransitionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.ValidEncryptionMaterialsTransition(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidDecryptionMaterialsTransition(AWS.Cryptography.MaterialProviders.ValidDecryptionMaterialsTransitionInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IValidDecryptionMaterialsTransitionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidDecryptionMaterialsTransitionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.ValidDecryptionMaterialsTransition(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void EncryptionMaterialsHasPlaintextDataKey(AWS.Cryptography.MaterialProviders.EncryptionMaterials input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.EncryptionMaterialsHasPlaintextDataKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void DecryptionMaterialsWithPlaintextDataKey(AWS.Cryptography.MaterialProviders.DecryptionMaterials input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.DecryptionMaterialsWithPlaintextDataKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo GetAlgorithmSuiteInfo(System.IO.MemoryStream input) {
 Dafny.ISequence<byte> internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_GetAlgorithmSuiteInfoInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.GetAlgorithmSuiteInfo(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(result.dtor_value);
}
 public void ValidAlgorithmSuiteInfo(AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.ValidAlgorithmSuiteInfo(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidateCommitmentPolicyOnEncrypt(AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnEncryptInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IValidateCommitmentPolicyOnEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnEncryptInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.ValidateCommitmentPolicyOnEncrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidateCommitmentPolicyOnDecrypt(AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnDecryptInput input) {
 software.amazon.cryptography.materialproviders.internaldafny.types._IValidateCommitmentPolicyOnDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnDecryptInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> result = _impl.ValidateCommitmentPolicyOnDecrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
}
}
