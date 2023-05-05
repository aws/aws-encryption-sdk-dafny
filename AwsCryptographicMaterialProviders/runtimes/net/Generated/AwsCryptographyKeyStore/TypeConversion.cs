// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace AWS.Cryptography.KeyStore {
 public static class TypeConversion {
 internal static AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput (Dafny.Aws.Cryptography.KeyStore.Types._IBranchKeyStatusResolutionInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.BranchKeyStatusResolutionInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.BranchKeyStatusResolutionInput)value; AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput converted = new AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IBranchKeyStatusResolutionInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput (AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.BranchKeyStatusResolutionInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput (Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyOutput)value; AWS.Cryptography.KeyStore.CreateKeyOutput converted = new AWS.Cryptography.KeyStore.CreateKeyOutput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput (AWS.Cryptography.KeyStore.CreateKeyOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyStoreInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput (Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreInput)value; AWS.Cryptography.KeyStore.CreateKeyStoreInput converted = new AWS.Cryptography.KeyStore.CreateKeyStoreInput();  return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput (AWS.Cryptography.KeyStore.CreateKeyStoreInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreInput (  ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyStoreOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput (Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreOutput)value; AWS.Cryptography.KeyStore.CreateKeyStoreOutput converted = new AWS.Cryptography.KeyStore.CreateKeyStoreOutput();  converted.TableArn = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn(concrete._tableArn); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._ICreateKeyStoreOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput (AWS.Cryptography.KeyStore.CreateKeyStoreOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn(value.TableArn) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetActiveBranchKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput (Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyInput)value; AWS.Cryptography.KeyStore.GetActiveBranchKeyInput converted = new AWS.Cryptography.KeyStore.GetActiveBranchKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput (AWS.Cryptography.KeyStore.GetActiveBranchKeyInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput (Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyOutput)value; AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput converted = new AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput();  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion(concrete._branchKeyVersion);
  converted.BranchKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey(concrete._branchKey); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetActiveBranchKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput (AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion(value.BranchKeyVersion) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey(value.BranchKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBeaconKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput (Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyInput)value; AWS.Cryptography.KeyStore.GetBeaconKeyInput converted = new AWS.Cryptography.KeyStore.GetBeaconKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput (AWS.Cryptography.KeyStore.GetBeaconKeyInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBeaconKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput (Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyOutput)value; AWS.Cryptography.KeyStore.GetBeaconKeyOutput converted = new AWS.Cryptography.KeyStore.GetBeaconKeyOutput();  converted.BeaconKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier(concrete._beaconKeyIdentifier);
  converted.BeaconKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey(concrete._beaconKey); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetBeaconKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput (AWS.Cryptography.KeyStore.GetBeaconKeyOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier(value.BeaconKeyIdentifier) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey(value.BeaconKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBranchKeyVersionInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput (Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionInput)value; AWS.Cryptography.KeyStore.GetBranchKeyVersionInput converted = new AWS.Cryptography.KeyStore.GetBranchKeyVersionInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier);
  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion(concrete._branchKeyVersion); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput (AWS.Cryptography.KeyStore.GetBranchKeyVersionInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion(value.BranchKeyVersion) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput (Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionOutput)value; AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput converted = new AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput();  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion(concrete._branchKeyVersion);
  converted.BranchKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey(concrete._branchKey); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetBranchKeyVersionOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput (AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion(value.BranchKeyVersion) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey(value.BranchKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput (Dafny.Aws.Cryptography.KeyStore.Types._IGetKeyStoreInfoOutput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.GetKeyStoreInfoOutput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.GetKeyStoreInfoOutput)value; AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput converted = new AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput();  converted.KeyStoreId = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId(concrete._keyStoreId);
  converted.KeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName(concrete._keyStoreName);
  converted.LogicalKeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName(concrete._logicalKeyStoreName);
  converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens(concrete._grantTokens);
  converted.KmsConfiguration = (AWS.Cryptography.KeyStore.KMSConfiguration) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration(concrete._kmsConfiguration); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IGetKeyStoreInfoOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput (AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.GetKeyStoreInfoOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId(value.KeyStoreId) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName(value.KeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName(value.LogicalKeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens(value.GrantTokens) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration(value.KmsConfiguration) ) ;
}
 internal static AWS.Cryptography.KeyStore.KeyStoreConfig FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig (Dafny.Aws.Cryptography.KeyStore.Types._IKeyStoreConfig value) {
 Dafny.Aws.Cryptography.KeyStore.Types.KeyStoreConfig concrete = (Dafny.Aws.Cryptography.KeyStore.Types.KeyStoreConfig)value; AWS.Cryptography.KeyStore.KeyStoreConfig converted = new AWS.Cryptography.KeyStore.KeyStoreConfig();  converted.DdbTableName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName(concrete._ddbTableName);
  converted.KmsConfiguration = (AWS.Cryptography.KeyStore.KMSConfiguration) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration(concrete._kmsConfiguration);
  converted.LogicalKeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName(concrete._logicalKeyStoreName);
 if (concrete._id.is_Some) converted.Id = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id(concrete._id);
 if (concrete._grantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens(concrete._grantTokens);
 if (concrete._ddbClient.is_Some) converted.DdbClient = (Amazon.DynamoDBv2.IAmazonDynamoDB) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient(concrete._ddbClient);
 if (concrete._kmsClient.is_Some) converted.KmsClient = (Amazon.KeyManagementService.IAmazonKeyManagementService) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient(concrete._kmsClient); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IKeyStoreConfig ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig (AWS.Cryptography.KeyStore.KeyStoreConfig value) {
 string var_id = value.IsSetId() ? value.Id : (string) null;
 System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens() ? value.GrantTokens : (System.Collections.Generic.List<string>) null;
 Amazon.DynamoDBv2.IAmazonDynamoDB var_ddbClient = value.IsSetDdbClient() ? value.DdbClient : (Amazon.DynamoDBv2.IAmazonDynamoDB) null;
 Amazon.KeyManagementService.IAmazonKeyManagementService var_kmsClient = value.IsSetKmsClient() ? value.KmsClient : (Amazon.KeyManagementService.IAmazonKeyManagementService) null;
 return new Dafny.Aws.Cryptography.KeyStore.Types.KeyStoreConfig ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName(value.DdbTableName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration(value.KmsConfiguration) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName(value.LogicalKeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id(var_id) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens(var_grantTokens) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient(var_ddbClient) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient(var_kmsClient) ) ;
}
 internal static AWS.Cryptography.KeyStore.KeyStoreException FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException (Dafny.Aws.Cryptography.KeyStore.Types.Error_KeyStoreException value) {
 return new AWS.Cryptography.KeyStore.KeyStoreException (
 FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message(value._message)
 ) ;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types.Error_KeyStoreException ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException (AWS.Cryptography.KeyStore.KeyStoreException value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.Error_KeyStoreException (
 ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message(value.Message)
 ) ;
}
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration (Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration value) {
 Dafny.Aws.Cryptography.KeyStore.Types.KMSConfiguration concrete = (Dafny.Aws.Cryptography.KeyStore.Types.KMSConfiguration)value;
 var converted = new AWS.Cryptography.KeyStore.KMSConfiguration(); if (value.is_kmsKeyArn) {
 converted.KmsKeyArn = FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn(concrete.dtor_kmsKeyArn);
 return converted;
}
throw new System.ArgumentException("Invalid AWS.Cryptography.KeyStore.KMSConfiguration state");
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
 if (value.IsSetKmsKeyArn()) {
 return Dafny.Aws.Cryptography.KeyStore.Types.KMSConfiguration.create(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn(value.KmsKeyArn));
}
throw new System.ArgumentException("Invalid AWS.Cryptography.KeyStore.KMSConfiguration state");
}
 internal static AWS.Cryptography.KeyStore.VersionKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput (Dafny.Aws.Cryptography.KeyStore.Types._IVersionKeyInput value) {
 Dafny.Aws.Cryptography.KeyStore.Types.VersionKeyInput concrete = (Dafny.Aws.Cryptography.KeyStore.Types.VersionKeyInput)value; AWS.Cryptography.KeyStore.VersionKeyInput converted = new AWS.Cryptography.KeyStore.VersionKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IVersionKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput (AWS.Cryptography.KeyStore.VersionKeyInput value) {

 return new Dafny.Aws.Cryptography.KeyStore.Types.VersionKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S8_TableArn(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn (string value) {
 return ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S8_TableArn(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion (string value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion (string value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList(value);
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens (System.Collections.Generic.List<string> value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList(value);
}
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration (Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration (Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static Dafny.Aws.Cryptography.KeyStore.Types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static Amazon.DynamoDBv2.IAmazonDynamoDB FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient (Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient> value) {
 return value.is_None ? (Amazon.DynamoDBv2.IAmazonDynamoDB) null : FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient (Amazon.DynamoDBv2.IAmazonDynamoDB value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient>.create_None() : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient>.create_Some(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference((Amazon.DynamoDBv2.IAmazonDynamoDB) value));
}
 internal static Amazon.KeyManagementService.IAmazonKeyManagementService FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient (Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms.Types.IKMSClient> value) {
 return value.is_None ? (Amazon.KeyManagementService.IAmazonKeyManagementService) null : FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms.Types.IKMSClient> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient (Amazon.KeyManagementService.IAmazonKeyManagementService value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms.Types.IKMSClient>.create_None() : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms.Types.IKMSClient>.create_Some(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference((Amazon.KeyManagementService.IAmazonKeyManagementService) value));
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn (Dafny.ISequence<char> value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S9_KmsKeyArn(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn (string value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S9_KmsKeyArn(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S8_TableArn (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S8_TableArn (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes (Dafny.ISequence<byte> value) {
 System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
return utf8.GetString(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S9_Utf8Bytes (string value) {
 System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret (Dafny.ISequence<byte> value) {
 return new System.IO.MemoryStream(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S6_Secret (System.IO.MemoryStream value) {
 return Dafny.Sequence<byte>.FromArray(value.ToArray());
}
 internal static string FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList__M6_member));
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value.Select(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList__M6_member).ToArray());
}
 public static Amazon.DynamoDBv2.IAmazonDynamoDB FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference (Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient value) {
 if (value is Com.Amazonaws.Dynamodb.DynamoDBv2Shim shim) { return shim._impl; } throw new System.ArgumentException("Custom implementations of Amazon.DynamoDBv2.IAmazonDynamoDBv2 are not supported yet");
}
 public static Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference (Amazon.DynamoDBv2.IAmazonDynamoDB value) {
 if (value is Amazon.DynamoDBv2.AmazonDynamoDBClient impl) { return new Com.Amazonaws.Dynamodb.DynamoDBv2Shim(impl); } throw new System.ArgumentException("Custom implementations of Amazon.DynamoDBv2.IAmazonDynamoDBv2 are not supported yet");
}
 public static Amazon.KeyManagementService.IAmazonKeyManagementService FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference (Dafny.Com.Amazonaws.Kms.Types.IKMSClient value) {
 if (value is Com.Amazonaws.Kms.KeyManagementServiceShim shim) { return shim._impl; } throw new System.ArgumentException("Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
}
 public static Dafny.Com.Amazonaws.Kms.Types.IKMSClient ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference (Amazon.KeyManagementService.IAmazonKeyManagementService value) {
 if (value is Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl) { return new Com.Amazonaws.Kms.KeyManagementServiceShim(impl); } throw new System.ArgumentException("Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S9_KmsKeyArn (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S9_KmsKeyArn (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList__M6_member (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_GrantTokenList__M6_member (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 public static System.Exception FromDafny_CommonError(Dafny.Aws.Cryptography.KeyStore.Types._IError value) {
 switch(value)
 {
 case Dafny.Aws.Cryptography.KeyStore.Types.Error_ComAmazonawsDynamodb dafnyVal:
  return Com.Amazonaws.Dynamodb.TypeConversion.FromDafny_CommonError(
    dafnyVal._ComAmazonawsDynamodb
  );
 case Dafny.Aws.Cryptography.KeyStore.Types.Error_KeyStoreException dafnyVal:
return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException(dafnyVal);
 case Dafny.Aws.Cryptography.KeyStore.Types.Error_CollectionOfErrors dafnyVal:
 return new CollectionOfErrors(new System.Collections.Generic.List<Exception>(dafnyVal._list.Elements.Select(x => TypeConversion.FromDafny_CommonError(x))));
 case Dafny.Aws.Cryptography.KeyStore.Types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static Dafny.Aws.Cryptography.KeyStore.Types._IError ToDafny_CommonError(System.Exception value) {
 switch (value.GetType().Namespace) {
 case "Com.Amazonaws.Dynamodb":
  return Dafny.Aws.Cryptography.KeyStore.Types.Error.create_ComAmazonawsDynamodb(
    Com.Amazonaws.Dynamodb.TypeConversion.ToDafny_CommonError(value)
  );
}
 switch (value)
 {
 case AWS.Cryptography.KeyStore.KeyStoreException exception:
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException(exception);
 case CollectionOfErrors collectionOfErrors:
 return new Dafny.Aws.Cryptography.KeyStore.Types.Error_CollectionOfErrors(
     Dafny.Sequence<Dafny.Aws.Cryptography.KeyStore.Types._IError>
     .FromArray(
         collectionOfErrors.list.Select
             (x => TypeConversion.ToDafny_CommonError(x))
         .ToArray()
     )
 );

 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new Dafny.Aws.Cryptography.KeyStore.Types.Error_Opaque(exception);
 case System.Exception exception:
 return new Dafny.Aws.Cryptography.KeyStore.Types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new Dafny.Aws.Cryptography.KeyStore.Types.Error_Opaque(value);
}
}
}
}
