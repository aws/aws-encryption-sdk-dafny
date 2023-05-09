// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace AWS.Cryptography.KeyStore {
 public static class TypeConversion {
 internal static AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput (software.amazon.cryptography.keystore.internaldafny.types._IBranchKeyStatusResolutionInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.BranchKeyStatusResolutionInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.BranchKeyStatusResolutionInput)value; AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput converted = new AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IBranchKeyStatusResolutionInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput (AWS.Cryptography.KeyStore.BranchKeyStatusResolutionInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.BranchKeyStatusResolutionInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S30_BranchKeyStatusResolutionInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput (software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput)value; AWS.Cryptography.KeyStore.CreateKeyOutput converted = new AWS.Cryptography.KeyStore.CreateKeyOutput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput (AWS.Cryptography.KeyStore.CreateKeyOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_CreateKeyOutput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyStoreInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput (software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput)value; AWS.Cryptography.KeyStore.CreateKeyStoreInput converted = new AWS.Cryptography.KeyStore.CreateKeyStoreInput();  return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S19_CreateKeyStoreInput (AWS.Cryptography.KeyStore.CreateKeyStoreInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput (  ) ;
}
 internal static AWS.Cryptography.KeyStore.CreateKeyStoreOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput (software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput)value; AWS.Cryptography.KeyStore.CreateKeyStoreOutput converted = new AWS.Cryptography.KeyStore.CreateKeyStoreOutput();  converted.TableArn = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn(concrete._tableArn); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput (AWS.Cryptography.KeyStore.CreateKeyStoreOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S20_CreateKeyStoreOutput__M8_tableArn(value.TableArn) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetActiveBranchKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput (software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput)value; AWS.Cryptography.KeyStore.GetActiveBranchKeyInput converted = new AWS.Cryptography.KeyStore.GetActiveBranchKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput (AWS.Cryptography.KeyStore.GetActiveBranchKeyInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S23_GetActiveBranchKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput (software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput)value; AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput converted = new AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput();  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion(concrete._branchKeyVersion);
  converted.BranchKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey(concrete._branchKey); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput (AWS.Cryptography.KeyStore.GetActiveBranchKeyOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M16_branchKeyVersion(value.BranchKeyVersion) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetActiveBranchKeyOutput__M9_branchKey(value.BranchKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBeaconKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput (software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput)value; AWS.Cryptography.KeyStore.GetBeaconKeyInput converted = new AWS.Cryptography.KeyStore.GetBeaconKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput (AWS.Cryptography.KeyStore.GetBeaconKeyInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_GetBeaconKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBeaconKeyOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput (software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput)value; AWS.Cryptography.KeyStore.GetBeaconKeyOutput converted = new AWS.Cryptography.KeyStore.GetBeaconKeyOutput();  converted.BeaconKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier(concrete._beaconKeyIdentifier);
  converted.BeaconKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey(concrete._beaconKey); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput (AWS.Cryptography.KeyStore.GetBeaconKeyOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M19_beaconKeyIdentifier(value.BeaconKeyIdentifier) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_GetBeaconKeyOutput__M9_beaconKey(value.BeaconKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBranchKeyVersionInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput (software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput)value; AWS.Cryptography.KeyStore.GetBranchKeyVersionInput converted = new AWS.Cryptography.KeyStore.GetBranchKeyVersionInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier);
  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion(concrete._branchKeyVersion); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput (AWS.Cryptography.KeyStore.GetBranchKeyVersionInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S24_GetBranchKeyVersionInput__M16_branchKeyVersion(value.BranchKeyVersion) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput (software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput)value; AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput converted = new AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput();  converted.BranchKeyVersion = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion(concrete._branchKeyVersion);
  converted.BranchKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey(concrete._branchKey); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput (AWS.Cryptography.KeyStore.GetBranchKeyVersionOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M16_branchKeyVersion(value.BranchKeyVersion) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S25_GetBranchKeyVersionOutput__M9_branchKey(value.BranchKey) ) ;
}
 internal static AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput (software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput value) {
 software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput concrete = (software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput)value; AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput converted = new AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput();  converted.KeyStoreId = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId(concrete._keyStoreId);
  converted.KeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName(concrete._keyStoreName);
  converted.LogicalKeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName(concrete._logicalKeyStoreName);
  converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens(concrete._grantTokens);
  converted.KmsConfiguration = (AWS.Cryptography.KeyStore.KMSConfiguration) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration(concrete._kmsConfiguration); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput (AWS.Cryptography.KeyStore.GetKeyStoreInfoOutput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M10_keyStoreId(value.KeyStoreId) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M12_keyStoreName(value.KeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M19_logicalKeyStoreName(value.LogicalKeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M11_grantTokens(value.GrantTokens) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration(value.KmsConfiguration) ) ;
}
 internal static AWS.Cryptography.KeyStore.KeyStoreConfig FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig (software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig value) {
 software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig concrete = (software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig)value; AWS.Cryptography.KeyStore.KeyStoreConfig converted = new AWS.Cryptography.KeyStore.KeyStoreConfig();  converted.DdbTableName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName(concrete._ddbTableName);
  converted.KmsConfiguration = (AWS.Cryptography.KeyStore.KMSConfiguration) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration(concrete._kmsConfiguration);
  converted.LogicalKeyStoreName = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName(concrete._logicalKeyStoreName);
 if (concrete._id.is_Some) converted.Id = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id(concrete._id);
 if (concrete._grantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens(concrete._grantTokens);
 if (concrete._ddbClient.is_Some) converted.DdbClient = (Amazon.DynamoDBv2.IAmazonDynamoDB) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient(concrete._ddbClient);
 if (concrete._kmsClient.is_Some) converted.KmsClient = (Amazon.KeyManagementService.IAmazonKeyManagementService) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient(concrete._kmsClient); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig (AWS.Cryptography.KeyStore.KeyStoreConfig value) {
 string var_id = value.IsSetId() ? value.Id : (string) null;
 System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens() ? value.GrantTokens : (System.Collections.Generic.List<string>) null;
 Amazon.DynamoDBv2.IAmazonDynamoDB var_ddbClient = value.IsSetDdbClient() ? value.DdbClient : (Amazon.DynamoDBv2.IAmazonDynamoDB) null;
 Amazon.KeyManagementService.IAmazonKeyManagementService var_kmsClient = value.IsSetKmsClient() ? value.KmsClient : (Amazon.KeyManagementService.IAmazonKeyManagementService) null;
 return new software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName(value.DdbTableName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration(value.KmsConfiguration) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M19_logicalKeyStoreName(value.LogicalKeyStoreName) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M2_id(var_id) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M11_grantTokens(var_grantTokens) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient(var_ddbClient) , ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient(var_kmsClient) ) ;
}
 internal static AWS.Cryptography.KeyStore.KeyStoreException FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException (software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException value) {
 return new AWS.Cryptography.KeyStore.KeyStoreException (
 FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException (AWS.Cryptography.KeyStore.KeyStoreException value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException (
 ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException__M7_message(value.Message)
 ) ;
}
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration (software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration value) {
 software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration concrete = (software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration)value;
 // BEGIN MANUAL EDIT
 var converted = new AWS.Cryptography.KeyStore.KMSConfiguration(); if (value.is_kmsKeyArn) {
 // END MANUAL EDIT
 converted.KmsKeyArn = FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn(concrete.dtor_kmsKeyArn);
 return converted;
}
throw new System.ArgumentException("Invalid AWS.Cryptography.KeyStore.KMSConfiguration state");
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
 if (value.IsSetKmsKeyArn()) {
 return software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration__M9_kmsKeyArn(value.KmsKeyArn));
}
throw new System.ArgumentException("Invalid AWS.Cryptography.KeyStore.KMSConfiguration state");
}
 internal static AWS.Cryptography.KeyStore.VersionKeyInput FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput (software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyInput value) {
 software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput concrete = (software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput)value; AWS.Cryptography.KeyStore.VersionKeyInput converted = new AWS.Cryptography.KeyStore.VersionKeyInput();  converted.BranchKeyIdentifier = (string) FromDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier(concrete._branchKeyIdentifier); return converted;
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyInput ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput (AWS.Cryptography.KeyStore.VersionKeyInput value) {

 return new software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput ( ToDafny_N3_aws__N12_cryptography__N8_keyStore__S15_VersionKeyInput__M19_branchKeyIdentifier(value.BranchKeyIdentifier) ) ;
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
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration (software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S21_GetKeyStoreInfoOutput__M16_kmsConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M12_ddbTableName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N8_dynamodb__S9_TableName(value);
}
 internal static AWS.Cryptography.KeyStore.KMSConfiguration FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration (software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration value) {
 return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S16_KMSConfiguration(value);
}
 internal static software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M16_kmsConfiguration (AWS.Cryptography.KeyStore.KMSConfiguration value) {
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
 internal static Amazon.DynamoDBv2.IAmazonDynamoDB FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient (Wrappers_Compile._IOption<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient> value) {
 return value.is_None ? (Amazon.DynamoDBv2.IAmazonDynamoDB) null : FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_ddbClient (Amazon.DynamoDBv2.IAmazonDynamoDB value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference((Amazon.DynamoDBv2.IAmazonDynamoDB) value));
}
 internal static Amazon.KeyManagementService.IAmazonKeyManagementService FromDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient> value) {
 return value.is_None ? (Amazon.KeyManagementService.IAmazonKeyManagementService) null : FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient> ToDafny_N3_aws__N12_cryptography__N8_keyStore__S14_KeyStoreConfig__M9_kmsClient (Amazon.KeyManagementService.IAmazonKeyManagementService value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference((Amazon.KeyManagementService.IAmazonKeyManagementService) value));
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
 public static Amazon.DynamoDBv2.IAmazonDynamoDB FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference (software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient value) {
 if (value is Com.Amazonaws.Dynamodb.DynamoDBv2Shim shim) { return shim._impl; } throw new System.ArgumentException("Custom implementations of Amazon.DynamoDBv2.IAmazonDynamoDBv2 are not supported yet");
}
 public static software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_DdbClientReference (Amazon.DynamoDBv2.IAmazonDynamoDB value) {
 if (value is Amazon.DynamoDBv2.AmazonDynamoDBClient impl) { return new Com.Amazonaws.Dynamodb.DynamoDBv2Shim(impl); } throw new System.ArgumentException("Custom implementations of Amazon.DynamoDBv2.IAmazonDynamoDBv2 are not supported yet");
}
 public static Amazon.KeyManagementService.IAmazonKeyManagementService FromDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference (software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient value) {
 if (value is Com.Amazonaws.Kms.KeyManagementServiceShim shim) { return shim._impl; } throw new System.ArgumentException("Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
}
 public static software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient ToDafny_N3_aws__N12_cryptography__N8_keyStore__S18_KmsClientReference (Amazon.KeyManagementService.IAmazonKeyManagementService value) {
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
 public static System.Exception FromDafny_CommonError(software.amazon.cryptography.keystore.internaldafny.types._IError value) {
 switch(value)
 {
 case software.amazon.cryptography.keystore.internaldafny.types.Error_ComAmazonawsDynamodb dafnyVal:
  return Com.Amazonaws.Dynamodb.TypeConversion.FromDafny_CommonError(
    dafnyVal._ComAmazonawsDynamodb
  );
 case software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException dafnyVal:
return FromDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException(dafnyVal);
 case software.amazon.cryptography.keystore.internaldafny.types.Error_CollectionOfErrors dafnyVal:
 return new CollectionOfErrors(new System.Collections.Generic.List<Exception>(dafnyVal._list.Elements.Select(x => TypeConversion.FromDafny_CommonError(x))));
 case software.amazon.cryptography.keystore.internaldafny.types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static software.amazon.cryptography.keystore.internaldafny.types._IError ToDafny_CommonError(System.Exception value) {
 switch (value.GetType().Namespace) {
 case "Com.Amazonaws.Dynamodb":
  return software.amazon.cryptography.keystore.internaldafny.types.Error.create_ComAmazonawsDynamodb(
    Com.Amazonaws.Dynamodb.TypeConversion.ToDafny_CommonError(value)
  );
}
 switch (value)
 {
 case AWS.Cryptography.KeyStore.KeyStoreException exception:
 return ToDafny_N3_aws__N12_cryptography__N8_keyStore__S17_KeyStoreException(exception);
 case CollectionOfErrors collectionOfErrors:
 return new software.amazon.cryptography.keystore.internaldafny.types.Error_CollectionOfErrors(
     Dafny.Sequence<software.amazon.cryptography.keystore.internaldafny.types._IError>
     .FromArray(
         collectionOfErrors.list.Select
             (x => TypeConversion.ToDafny_CommonError(x))
         .ToArray()
     )
 );

 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new software.amazon.cryptography.keystore.internaldafny.types.Error_Opaque(exception);
 case System.Exception exception:
 return new software.amazon.cryptography.keystore.internaldafny.types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new software.amazon.cryptography.keystore.internaldafny.types.Error_Opaque(value);
}
}
}
}
