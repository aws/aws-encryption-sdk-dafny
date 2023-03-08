// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProviders;
 using Dafny.Aws.Cryptography.MaterialProviders.Types; namespace AWS.Cryptography.MaterialProviders {
 public class MaterialProviders {
 private readonly Dafny.Aws.Cryptography.MaterialProviders.Types.IAwsCryptographicMaterialProvidersClient _impl;
 public MaterialProviders(AWS.Cryptography.MaterialProviders.MaterialProvidersConfig input)
 {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IMaterialProvidersConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_MaterialProvidersConfig(input);
 var result = Dafny.Aws.Cryptography.MaterialProviders.__default.MaterialProviders(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateAwsKmsKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsDiscoveryKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsDiscoveryKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateAwsKmsDiscoveryKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsDiscoveryKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMultiKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S29_CreateAwsKmsMultiKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsDiscoveryMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryMultiKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsMrkKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsMrkKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkMultiKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateAwsKmsMrkMultiKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsMrkMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkDiscoveryKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkDiscoveryKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsMrkDiscoveryKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsMrkDiscoveryKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkDiscoveryMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsMrkDiscoveryMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsHierarchicalKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsHierarchicalKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsHierarchicalKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsHierarchicalKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsHierarchicalKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateMultiKeyring(AWS.Cryptography.MaterialProviders.CreateMultiKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateMultiKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_CreateMultiKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateMultiKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateRawAesKeyring(AWS.Cryptography.MaterialProviders.CreateRawAesKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateRawAesKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawAesKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateRawAesKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateRawRsaKeyring(AWS.Cryptography.MaterialProviders.CreateRawRsaKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateRawRsaKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawRsaKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateRawRsaKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateAwsKmsRsaKeyring(AWS.Cryptography.MaterialProviders.CreateAwsKmsRsaKeyringInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsRsaKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsRsaKeyringInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateAwsKmsRsaKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(AWS.Cryptography.MaterialProviders.CreateDefaultCryptographicMaterialsManagerInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateDefaultCryptographicMaterialsManagerInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateDefaultCryptographicMaterialsManager(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateCryptographicMaterialsManagerOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IClientSupplier CreateDefaultClientSupplier(AWS.Cryptography.MaterialProviders.CreateDefaultClientSupplierInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateDefaultClientSupplierInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateDefaultClientSupplierInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.CreateDefaultClientSupplier(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateDefaultClientSupplierOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.EncryptionMaterials InitializeEncryptionMaterials(AWS.Cryptography.MaterialProviders.InitializeEncryptionMaterialsInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IInitializeEncryptionMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeEncryptionMaterialsInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.InitializeEncryptionMaterials(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.DecryptionMaterials InitializeDecryptionMaterials(AWS.Cryptography.MaterialProviders.InitializeDecryptionMaterialsInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IInitializeDecryptionMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeDecryptionMaterialsInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.InitializeDecryptionMaterials(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(result.dtor_value);
}
 public void ValidEncryptionMaterialsTransition(AWS.Cryptography.MaterialProviders.ValidEncryptionMaterialsTransitionInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IValidEncryptionMaterialsTransitionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidEncryptionMaterialsTransitionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.ValidEncryptionMaterialsTransition(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidDecryptionMaterialsTransition(AWS.Cryptography.MaterialProviders.ValidDecryptionMaterialsTransitionInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IValidDecryptionMaterialsTransitionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidDecryptionMaterialsTransitionInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.ValidDecryptionMaterialsTransition(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void EncryptionMaterialsHasPlaintextDataKey(AWS.Cryptography.MaterialProviders.EncryptionMaterials input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.EncryptionMaterialsHasPlaintextDataKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void DecryptionMaterialsWithPlaintextDataKey(AWS.Cryptography.MaterialProviders.DecryptionMaterials input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.DecryptionMaterialsWithPlaintextDataKey(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo GetAlgorithmSuiteInfo(System.IO.MemoryStream input) {
 Dafny.ISequence<byte> internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_GetAlgorithmSuiteInfoInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.GetAlgorithmSuiteInfo(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(result.dtor_value);
}
 public void ValidAlgorithmSuiteInfo(AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.ValidAlgorithmSuiteInfo(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidateCommitmentPolicyOnEncrypt(AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnEncryptInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IValidateCommitmentPolicyOnEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnEncryptInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.ValidateCommitmentPolicyOnEncrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
 public void ValidateCommitmentPolicyOnDecrypt(AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnDecryptInput input) {
 Dafny.Aws.Cryptography.MaterialProviders.Types._IValidateCommitmentPolicyOnDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnDecryptInput(input);
 Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = _impl.ValidateCommitmentPolicyOnDecrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 
}
}
}
