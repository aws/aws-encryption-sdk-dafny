// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace Com.Amazonaws.Kms {
 public static class TypeConversion {
 internal static Amazon.KeyManagementService.AlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec (software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec value) {
 if (value.is_RSAES__PKCS1__V1__5) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_PKCS1_V1_5;
 if (value.is_RSAES__OAEP__SHA__1) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_1;
 if (value.is_RSAES__OAEP__SHA__256) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_256;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.AlgorithmSpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec (Amazon.KeyManagementService.AlgorithmSpec value) {
 if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_PKCS1_V1_5.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec.create_RSAES__PKCS1__V1__5();
 if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_1.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec.create_RSAES__OAEP__SHA__1();
 if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec.create_RSAES__OAEP__SHA__256();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.AlgorithmSpec value");
}
 internal static Amazon.KeyManagementService.Model.AlreadyExistsException FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException (software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException value) {
 return new Amazon.KeyManagementService.Model.AlreadyExistsException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException (Amazon.KeyManagementService.Model.AlreadyExistsException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CancelKeyDeletionRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest (software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest)value; Amazon.KeyManagementService.Model.CancelKeyDeletionRequest converted = new Amazon.KeyManagementService.Model.CancelKeyDeletionRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest (Amazon.KeyManagementService.Model.CancelKeyDeletionRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.CancelKeyDeletionResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse (software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse)value; Amazon.KeyManagementService.Model.CancelKeyDeletionResponse converted = new Amazon.KeyManagementService.Model.CancelKeyDeletionResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse (Amazon.KeyManagementService.Model.CancelKeyDeletionResponse value) {
 string var_keyId = value.KeyId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(var_keyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.CloudHsmClusterInUseException FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException value) {
 return new Amazon.KeyManagementService.Model.CloudHsmClusterInUseException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException (Amazon.KeyManagementService.Model.CloudHsmClusterInUseException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException value) {
 return new Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException (Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException value) {
 return new Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException (Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException value) {
 return new Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException (Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException value) {
 return new Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException (Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest (software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest)value; Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest converted = new Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest();  converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest (Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(value.CustomKeyStoreId) ) ;
}
 internal static Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse (software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse)value; Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse converted = new Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse();  return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse (Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse (  ) ;
}
 internal static Amazon.KeyManagementService.ConnectionErrorCodeType FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType (software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType value) {
 if (value.is_INVALID__CREDENTIALS) return Amazon.KeyManagementService.ConnectionErrorCodeType.INVALID_CREDENTIALS;
 if (value.is_CLUSTER__NOT__FOUND) return Amazon.KeyManagementService.ConnectionErrorCodeType.CLUSTER_NOT_FOUND;
 if (value.is_NETWORK__ERRORS) return Amazon.KeyManagementService.ConnectionErrorCodeType.NETWORK_ERRORS;
 if (value.is_INTERNAL__ERROR) return Amazon.KeyManagementService.ConnectionErrorCodeType.INTERNAL_ERROR;
 if (value.is_INSUFFICIENT__CLOUDHSM__HSMS) return Amazon.KeyManagementService.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS;
 if (value.is_USER__LOCKED__OUT) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOCKED_OUT;
 if (value.is_USER__NOT__FOUND) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_NOT_FOUND;
 if (value.is_USER__LOGGED__IN) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOGGED_IN;
 if (value.is_SUBNET__NOT__FOUND) return Amazon.KeyManagementService.ConnectionErrorCodeType.SUBNET_NOT_FOUND;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionErrorCodeType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType (Amazon.KeyManagementService.ConnectionErrorCodeType value) {
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.INVALID_CREDENTIALS.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_INVALID__CREDENTIALS();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.CLUSTER_NOT_FOUND.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_CLUSTER__NOT__FOUND();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.NETWORK_ERRORS.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_NETWORK__ERRORS();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.INTERNAL_ERROR.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_INTERNAL__ERROR();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_INSUFFICIENT__CLOUDHSM__HSMS();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOCKED_OUT.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_USER__LOCKED__OUT();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_NOT_FOUND.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_USER__NOT__FOUND();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOGGED_IN.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_USER__LOGGED__IN();
 if (Amazon.KeyManagementService.ConnectionErrorCodeType.SUBNET_NOT_FOUND.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.create_SUBNET__NOT__FOUND();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionErrorCodeType value");
}
 internal static Amazon.KeyManagementService.ConnectionStateType FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType (software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType value) {
 if (value.is_CONNECTED) return Amazon.KeyManagementService.ConnectionStateType.CONNECTED;
 if (value.is_CONNECTING) return Amazon.KeyManagementService.ConnectionStateType.CONNECTING;
 if (value.is_FAILED) return Amazon.KeyManagementService.ConnectionStateType.FAILED;
 if (value.is_DISCONNECTED) return Amazon.KeyManagementService.ConnectionStateType.DISCONNECTED;
 if (value.is_DISCONNECTING) return Amazon.KeyManagementService.ConnectionStateType.DISCONNECTING;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionStateType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType (Amazon.KeyManagementService.ConnectionStateType value) {
 if (Amazon.KeyManagementService.ConnectionStateType.CONNECTED.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.create_CONNECTED();
 if (Amazon.KeyManagementService.ConnectionStateType.CONNECTING.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.create_CONNECTING();
 if (Amazon.KeyManagementService.ConnectionStateType.FAILED.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.create_FAILED();
 if (Amazon.KeyManagementService.ConnectionStateType.DISCONNECTED.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.create_DISCONNECTED();
 if (Amazon.KeyManagementService.ConnectionStateType.DISCONNECTING.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.create_DISCONNECTING();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionStateType value");
}
 internal static Amazon.KeyManagementService.Model.CreateAliasRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest (software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest)value; Amazon.KeyManagementService.Model.CreateAliasRequest converted = new Amazon.KeyManagementService.Model.CreateAliasRequest();  converted.AliasName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(concrete._AliasName);
  converted.TargetKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(concrete._TargetKeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest (Amazon.KeyManagementService.Model.CreateAliasRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(value.AliasName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(value.TargetKeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest (software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest)value; Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest converted = new Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest();  converted.CustomKeyStoreName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(concrete._CustomKeyStoreName);
  converted.CloudHsmClusterId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(concrete._CloudHsmClusterId);
  converted.TrustAnchorCertificate = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(concrete._TrustAnchorCertificate);
  converted.KeyStorePassword = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(concrete._KeyStorePassword); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest (Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(value.CustomKeyStoreName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(value.CloudHsmClusterId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(value.TrustAnchorCertificate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(value.KeyStorePassword) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse (software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse)value; Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse converted = new Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse(); if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(concrete._CustomKeyStoreId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse (Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse value) {
 string var_customKeyStoreId = value.CustomKeyStoreId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(var_customKeyStoreId) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateGrantRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest (software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest)value; Amazon.KeyManagementService.Model.CreateGrantRequest converted = new Amazon.KeyManagementService.Model.CreateGrantRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(concrete._KeyId);
  converted.GranteePrincipal = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(concrete._GranteePrincipal);
 if (concrete._RetiringPrincipal.is_Some) converted.RetiringPrincipal = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(concrete._RetiringPrincipal);
  converted.Operations = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(concrete._Operations);
 if (concrete._Constraints.is_Some) converted.Constraints = (Amazon.KeyManagementService.Model.GrantConstraints) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(concrete._Constraints);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(concrete._GrantTokens);
 if (concrete._Name.is_Some) converted.Name = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(concrete._Name); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest (Amazon.KeyManagementService.Model.CreateGrantRequest value) {
 string var_retiringPrincipal = value.RetiringPrincipal;
 Amazon.KeyManagementService.Model.GrantConstraints var_constraints = value.Constraints;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 string var_name = value.Name;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(value.GranteePrincipal) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(var_retiringPrincipal) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(value.Operations) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(var_constraints) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(var_grantTokens) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(var_name) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateGrantResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse (software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse)value; Amazon.KeyManagementService.Model.CreateGrantResponse converted = new Amazon.KeyManagementService.Model.CreateGrantResponse(); if (concrete._GrantToken.is_Some) converted.GrantToken = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(concrete._GrantToken);
 if (concrete._GrantId.is_Some) converted.GrantId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(concrete._GrantId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse (Amazon.KeyManagementService.Model.CreateGrantResponse value) {
 string var_grantToken = value.GrantToken;
 string var_grantId = value.GrantId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(var_grantToken) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(var_grantId) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest)value; Amazon.KeyManagementService.Model.CreateKeyRequest converted = new Amazon.KeyManagementService.Model.CreateKeyRequest(); if (concrete._Policy.is_Some) converted.Policy = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(concrete._Policy);
 if (concrete._Description.is_Some) converted.Description = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(concrete._Description);
 if (concrete._KeyUsage.is_Some) converted.KeyUsage = (Amazon.KeyManagementService.KeyUsageType) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(concrete._KeyUsage);
 if (concrete._CustomerMasterKeySpec.is_Some) converted.CustomerMasterKeySpec = (Amazon.KeyManagementService.CustomerMasterKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(concrete._CustomerMasterKeySpec);
 if (concrete._KeySpec.is_Some) converted.KeySpec = (Amazon.KeyManagementService.KeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(concrete._KeySpec);
 if (concrete._Origin.is_Some) converted.Origin = (Amazon.KeyManagementService.OriginType) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(concrete._Origin);
 if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId);
 if (concrete._BypassPolicyLockoutSafetyCheck.is_Some) converted.BypassPolicyLockoutSafetyCheck = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(concrete._BypassPolicyLockoutSafetyCheck);
 if (concrete._Tags.is_Some) converted.Tags = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(concrete._Tags);
 if (concrete._MultiRegion.is_Some) converted.MultiRegion = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(concrete._MultiRegion); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest (Amazon.KeyManagementService.Model.CreateKeyRequest value) {
 string var_policy = value.Policy;
 string var_description = value.Description;
 Amazon.KeyManagementService.KeyUsageType var_keyUsage = value.KeyUsage;
 Amazon.KeyManagementService.CustomerMasterKeySpec var_customerMasterKeySpec = value.CustomerMasterKeySpec;
 Amazon.KeyManagementService.KeySpec var_keySpec = value.KeySpec;
 Amazon.KeyManagementService.OriginType var_origin = value.Origin;
 string var_customKeyStoreId = value.CustomKeyStoreId;
 bool? var_bypassPolicyLockoutSafetyCheck = value.BypassPolicyLockoutSafetyCheck;
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> var_tags = value.Tags;
 bool? var_multiRegion = value.MultiRegion;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(var_policy) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(var_description) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(var_keyUsage) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(var_customerMasterKeySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(var_keySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(var_origin) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(var_customKeyStoreId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(var_bypassPolicyLockoutSafetyCheck) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(var_tags) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(var_multiRegion) ) ;
}
 internal static Amazon.KeyManagementService.Model.CreateKeyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse (software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse)value; Amazon.KeyManagementService.Model.CreateKeyResponse converted = new Amazon.KeyManagementService.Model.CreateKeyResponse(); if (concrete._KeyMetadata.is_Some) converted.KeyMetadata = (Amazon.KeyManagementService.Model.KeyMetadata) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(concrete._KeyMetadata); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse (Amazon.KeyManagementService.Model.CreateKeyResponse value) {
 Amazon.KeyManagementService.Model.KeyMetadata var_keyMetadata = value.KeyMetadata;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(var_keyMetadata) ) ;
}
 internal static Amazon.KeyManagementService.CustomerMasterKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec (software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec value) {
 if (value.is_RSA__2048) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_2048;
 if (value.is_RSA__3072) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_3072;
 if (value.is_RSA__4096) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_4096;
 if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P256;
 if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P384;
 if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P521;
 if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_SECG_P256K1;
 if (value.is_SYMMETRIC__DEFAULT) return Amazon.KeyManagementService.CustomerMasterKeySpec.SYMMETRIC_DEFAULT;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.CustomerMasterKeySpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec (Amazon.KeyManagementService.CustomerMasterKeySpec value) {
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_2048.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_RSA__2048();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_3072.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_RSA__3072();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_4096.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_RSA__4096();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_ECC__NIST__P256();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_ECC__NIST__P384();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P521.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_ECC__NIST__P521();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_SECG_P256K1.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_ECC__SECG__P256K1();
 if (Amazon.KeyManagementService.CustomerMasterKeySpec.SYMMETRIC_DEFAULT.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.create_SYMMETRIC__DEFAULT();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.CustomerMasterKeySpec value");
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException value) {
 return new Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException (Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException value) {
 return new Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException (Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException value) {
 return new Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException (Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException (software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException value) {
 return new Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException (Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.DataKeyPairSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec (software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec value) {
 if (value.is_RSA__2048) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_2048;
 if (value.is_RSA__3072) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_3072;
 if (value.is_RSA__4096) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_4096;
 if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P256;
 if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P384;
 if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P521;
 if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_SECG_P256K1;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeyPairSpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec (Amazon.KeyManagementService.DataKeyPairSpec value) {
 if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_2048.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_RSA__2048();
 if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_3072.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_RSA__3072();
 if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_4096.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_RSA__4096();
 if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_ECC__NIST__P256();
 if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_ECC__NIST__P384();
 if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P521.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_ECC__NIST__P521();
 if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_SECG_P256K1.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.create_ECC__SECG__P256K1();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeyPairSpec value");
}
 internal static Amazon.KeyManagementService.DataKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec (software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec value) {
 if (value.is_AES__256) return Amazon.KeyManagementService.DataKeySpec.AES_256;
 if (value.is_AES__128) return Amazon.KeyManagementService.DataKeySpec.AES_128;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeySpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec (Amazon.KeyManagementService.DataKeySpec value) {
 if (Amazon.KeyManagementService.DataKeySpec.AES_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.create_AES__256();
 if (Amazon.KeyManagementService.DataKeySpec.AES_128.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.create_AES__128();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeySpec value");
}
 internal static Amazon.KeyManagementService.Model.DecryptRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest)value; Amazon.KeyManagementService.Model.DecryptRequest converted = new Amazon.KeyManagementService.Model.DecryptRequest();  converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(concrete._EncryptionContext);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(concrete._GrantTokens);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(concrete._KeyId);
 if (concrete._EncryptionAlgorithm.is_Some) converted.EncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(concrete._EncryptionAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest (Amazon.KeyManagementService.Model.DecryptRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 string var_keyId = value.KeyId;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_encryptionAlgorithm = value.EncryptionAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(value.CiphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(var_grantTokens) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(var_encryptionAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.DecryptResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse (software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse)value; Amazon.KeyManagementService.Model.DecryptResponse converted = new Amazon.KeyManagementService.Model.DecryptResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(concrete._KeyId);
 if (concrete._Plaintext.is_Some) converted.Plaintext = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(concrete._Plaintext);
 if (concrete._EncryptionAlgorithm.is_Some) converted.EncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(concrete._EncryptionAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse (Amazon.KeyManagementService.Model.DecryptResponse value) {
 string var_keyId = value.KeyId;
 System.IO.MemoryStream var_plaintext = value.Plaintext;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_encryptionAlgorithm = value.EncryptionAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(var_plaintext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(var_encryptionAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.DeleteAliasRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest)value; Amazon.KeyManagementService.Model.DeleteAliasRequest converted = new Amazon.KeyManagementService.Model.DeleteAliasRequest();  converted.AliasName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(concrete._AliasName); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest (Amazon.KeyManagementService.Model.DeleteAliasRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(value.AliasName) ) ;
}
 internal static Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest)value; Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest converted = new Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest();  converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest (Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(value.CustomKeyStoreId) ) ;
}
 internal static Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse (software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse)value; Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse converted = new Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse();  return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse (Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse (  ) ;
}
 internal static Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest)value; Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest converted = new Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest (Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.DependencyTimeoutException FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException (software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException value) {
 return new Amazon.KeyManagementService.Model.DependencyTimeoutException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException (Amazon.KeyManagementService.Model.DependencyTimeoutException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest)value; Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest converted = new Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest(); if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId);
 if (concrete._CustomKeyStoreName.is_Some) converted.CustomKeyStoreName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(concrete._CustomKeyStoreName);
 if (concrete._Limit.is_Some) converted.Limit = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(concrete._Limit);
 if (concrete._Marker.is_Some) converted.Marker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(concrete._Marker); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest (Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest value) {
 string var_customKeyStoreId = value.CustomKeyStoreId;
 string var_customKeyStoreName = value.CustomKeyStoreName;
 int? var_limit = value.Limit;
 string var_marker = value.Marker;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(var_customKeyStoreId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(var_customKeyStoreName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(var_limit) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(var_marker) ) ;
}
 internal static Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse (software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse)value; Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse converted = new Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse(); if (concrete._CustomKeyStores.is_Some) converted.CustomKeyStores = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>) FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(concrete._CustomKeyStores);
 if (concrete._NextMarker.is_Some) converted.NextMarker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(concrete._NextMarker);
 if (concrete._Truncated.is_Some) converted.Truncated = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(concrete._Truncated); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse (Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse value) {
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> var_customKeyStores = value.CustomKeyStores;
 string var_nextMarker = value.NextMarker;
 bool? var_truncated = value.Truncated;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(var_customKeyStores) , ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(var_nextMarker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(var_truncated) ) ;
}
 internal static Amazon.KeyManagementService.Model.DescribeKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest)value; Amazon.KeyManagementService.Model.DescribeKeyRequest converted = new Amazon.KeyManagementService.Model.DescribeKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(concrete._KeyId);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest (Amazon.KeyManagementService.Model.DescribeKeyRequest value) {
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.DescribeKeyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse)value; Amazon.KeyManagementService.Model.DescribeKeyResponse converted = new Amazon.KeyManagementService.Model.DescribeKeyResponse(); if (concrete._KeyMetadata.is_Some) converted.KeyMetadata = (Amazon.KeyManagementService.Model.KeyMetadata) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(concrete._KeyMetadata); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse (Amazon.KeyManagementService.Model.DescribeKeyResponse value) {
 Amazon.KeyManagementService.Model.KeyMetadata var_keyMetadata = value.KeyMetadata;
 return new software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(var_keyMetadata) ) ;
}
 internal static Amazon.KeyManagementService.Model.DisabledException FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException (software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException value) {
 return new Amazon.KeyManagementService.Model.DisabledException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException (Amazon.KeyManagementService.Model.DisabledException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.DisableKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest)value; Amazon.KeyManagementService.Model.DisableKeyRequest converted = new Amazon.KeyManagementService.Model.DisableKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest (Amazon.KeyManagementService.Model.DisableKeyRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.DisableKeyRotationRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest)value; Amazon.KeyManagementService.Model.DisableKeyRotationRequest converted = new Amazon.KeyManagementService.Model.DisableKeyRotationRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest (Amazon.KeyManagementService.Model.DisableKeyRotationRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest (software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest)value; Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest converted = new Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest();  converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest (Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(value.CustomKeyStoreId) ) ;
}
 internal static Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse (software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse)value; Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse converted = new Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse();  return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse (Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse (  ) ;
}
 internal static Amazon.KeyManagementService.Model.EnableKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest)value; Amazon.KeyManagementService.Model.EnableKeyRequest converted = new Amazon.KeyManagementService.Model.EnableKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest (Amazon.KeyManagementService.Model.EnableKeyRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.EnableKeyRotationRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest (software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest)value; Amazon.KeyManagementService.Model.EnableKeyRotationRequest converted = new Amazon.KeyManagementService.Model.EnableKeyRotationRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest (Amazon.KeyManagementService.Model.EnableKeyRotationRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec value) {
 if (value.is_SYMMETRIC__DEFAULT) return Amazon.KeyManagementService.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT;
 if (value.is_RSAES__OAEP__SHA__1) return Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1;
 if (value.is_RSAES__OAEP__SHA__256) return Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.EncryptionAlgorithmSpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_SYMMETRIC__DEFAULT();
 if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1();
 if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.EncryptionAlgorithmSpec value");
}
 internal static Amazon.KeyManagementService.Model.EncryptRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest)value; Amazon.KeyManagementService.Model.EncryptRequest converted = new Amazon.KeyManagementService.Model.EncryptRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(concrete._KeyId);
  converted.Plaintext = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(concrete._Plaintext);
 if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(concrete._EncryptionContext);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(concrete._GrantTokens);
 if (concrete._EncryptionAlgorithm.is_Some) converted.EncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(concrete._EncryptionAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest (Amazon.KeyManagementService.Model.EncryptRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_encryptionAlgorithm = value.EncryptionAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(value.Plaintext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(var_grantTokens) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(var_encryptionAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.EncryptResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse)value; Amazon.KeyManagementService.Model.EncryptResponse converted = new Amazon.KeyManagementService.Model.EncryptResponse(); if (concrete._CiphertextBlob.is_Some) converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(concrete._KeyId);
 if (concrete._EncryptionAlgorithm.is_Some) converted.EncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(concrete._EncryptionAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse (Amazon.KeyManagementService.Model.EncryptResponse value) {
 System.IO.MemoryStream var_ciphertextBlob = value.CiphertextBlob;
 string var_keyId = value.KeyId;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_encryptionAlgorithm = value.EncryptionAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(var_ciphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(var_encryptionAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.ExpirationModelType FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType (software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType value) {
 if (value.is_KEY__MATERIAL__EXPIRES) return Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_EXPIRES;
 if (value.is_KEY__MATERIAL__DOES__NOT__EXPIRE) return Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ExpirationModelType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType (Amazon.KeyManagementService.ExpirationModelType value) {
 if (Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_EXPIRES.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType.create_KEY__MATERIAL__EXPIRES();
 if (Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType.create_KEY__MATERIAL__DOES__NOT__EXPIRE();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ExpirationModelType value");
}
 internal static Amazon.KeyManagementService.Model.ExpiredImportTokenException FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException (software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException value) {
 return new Amazon.KeyManagementService.Model.ExpiredImportTokenException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException (Amazon.KeyManagementService.Model.ExpiredImportTokenException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest)value; Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest converted = new Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest(); if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(concrete._EncryptionContext);
  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(concrete._KeyId);
  converted.KeyPairSpec = (Amazon.KeyManagementService.DataKeyPairSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(concrete._KeyPairSpec);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest (Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(value.KeyPairSpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse)value; Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse converted = new Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse(); if (concrete._PrivateKeyCiphertextBlob.is_Some) converted.PrivateKeyCiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(concrete._PrivateKeyCiphertextBlob);
 if (concrete._PrivateKeyPlaintext.is_Some) converted.PrivateKeyPlaintext = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(concrete._PrivateKeyPlaintext);
 if (concrete._PublicKey.is_Some) converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(concrete._PublicKey);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(concrete._KeyId);
 if (concrete._KeyPairSpec.is_Some) converted.KeyPairSpec = (Amazon.KeyManagementService.DataKeyPairSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(concrete._KeyPairSpec); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse (Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse value) {
 System.IO.MemoryStream var_privateKeyCiphertextBlob = value.PrivateKeyCiphertextBlob;
 System.IO.MemoryStream var_privateKeyPlaintext = value.PrivateKeyPlaintext;
 System.IO.MemoryStream var_publicKey = value.PublicKey;
 string var_keyId = value.KeyId;
 Amazon.KeyManagementService.DataKeyPairSpec var_keyPairSpec = value.KeyPairSpec;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(var_privateKeyCiphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(var_privateKeyPlaintext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(var_publicKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(var_keyPairSpec) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest)value; Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest converted = new Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest(); if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(concrete._EncryptionContext);
  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(concrete._KeyId);
  converted.KeyPairSpec = (Amazon.KeyManagementService.DataKeyPairSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(concrete._KeyPairSpec);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest (Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(value.KeyPairSpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse)value; Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse converted = new Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse(); if (concrete._PrivateKeyCiphertextBlob.is_Some) converted.PrivateKeyCiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(concrete._PrivateKeyCiphertextBlob);
 if (concrete._PublicKey.is_Some) converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(concrete._PublicKey);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(concrete._KeyId);
 if (concrete._KeyPairSpec.is_Some) converted.KeyPairSpec = (Amazon.KeyManagementService.DataKeyPairSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(concrete._KeyPairSpec); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse (Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse value) {
 System.IO.MemoryStream var_privateKeyCiphertextBlob = value.PrivateKeyCiphertextBlob;
 System.IO.MemoryStream var_publicKey = value.PublicKey;
 string var_keyId = value.KeyId;
 Amazon.KeyManagementService.DataKeyPairSpec var_keyPairSpec = value.KeyPairSpec;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(var_privateKeyCiphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(var_publicKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(var_keyPairSpec) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest)value; Amazon.KeyManagementService.Model.GenerateDataKeyRequest converted = new Amazon.KeyManagementService.Model.GenerateDataKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(concrete._KeyId);
 if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(concrete._EncryptionContext);
 if (concrete._NumberOfBytes.is_Some) converted.NumberOfBytes = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(concrete._NumberOfBytes);
 if (concrete._KeySpec.is_Some) converted.KeySpec = (Amazon.KeyManagementService.DataKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(concrete._KeySpec);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest (Amazon.KeyManagementService.Model.GenerateDataKeyRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 int? var_numberOfBytes = value.NumberOfBytes;
 Amazon.KeyManagementService.DataKeySpec var_keySpec = value.KeySpec;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(var_numberOfBytes) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(var_keySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse)value; Amazon.KeyManagementService.Model.GenerateDataKeyResponse converted = new Amazon.KeyManagementService.Model.GenerateDataKeyResponse(); if (concrete._CiphertextBlob.is_Some) converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._Plaintext.is_Some) converted.Plaintext = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(concrete._Plaintext);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse (Amazon.KeyManagementService.Model.GenerateDataKeyResponse value) {
 System.IO.MemoryStream var_ciphertextBlob = value.CiphertextBlob;
 System.IO.MemoryStream var_plaintext = value.Plaintext;
 string var_keyId = value.KeyId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(var_ciphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(var_plaintext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(var_keyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest)value; Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest converted = new Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(concrete._KeyId);
 if (concrete._EncryptionContext.is_Some) converted.EncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(concrete._EncryptionContext);
 if (concrete._KeySpec.is_Some) converted.KeySpec = (Amazon.KeyManagementService.DataKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(concrete._KeySpec);
 if (concrete._NumberOfBytes.is_Some) converted.NumberOfBytes = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(concrete._NumberOfBytes);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest (Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.EncryptionContext;
 Amazon.KeyManagementService.DataKeySpec var_keySpec = value.KeySpec;
 int? var_numberOfBytes = value.NumberOfBytes;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(var_encryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(var_keySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(var_numberOfBytes) , ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse)value; Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse converted = new Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse(); if (concrete._CiphertextBlob.is_Some) converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse (Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse value) {
 System.IO.MemoryStream var_ciphertextBlob = value.CiphertextBlob;
 string var_keyId = value.KeyId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(var_ciphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(var_keyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateRandomRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest)value; Amazon.KeyManagementService.Model.GenerateRandomRequest converted = new Amazon.KeyManagementService.Model.GenerateRandomRequest(); if (concrete._NumberOfBytes.is_Some) converted.NumberOfBytes = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(concrete._NumberOfBytes);
 if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest (Amazon.KeyManagementService.Model.GenerateRandomRequest value) {
 int? var_numberOfBytes = value.NumberOfBytes;
 string var_customKeyStoreId = value.CustomKeyStoreId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(var_numberOfBytes) , ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(var_customKeyStoreId) ) ;
}
 internal static Amazon.KeyManagementService.Model.GenerateRandomResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse)value; Amazon.KeyManagementService.Model.GenerateRandomResponse converted = new Amazon.KeyManagementService.Model.GenerateRandomResponse(); if (concrete._Plaintext.is_Some) converted.Plaintext = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(concrete._Plaintext); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse (Amazon.KeyManagementService.Model.GenerateRandomResponse value) {
 System.IO.MemoryStream var_plaintext = value.Plaintext;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(var_plaintext) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetKeyPolicyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest)value; Amazon.KeyManagementService.Model.GetKeyPolicyRequest converted = new Amazon.KeyManagementService.Model.GetKeyPolicyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(concrete._KeyId);
  converted.PolicyName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(concrete._PolicyName); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest (Amazon.KeyManagementService.Model.GetKeyPolicyRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(value.PolicyName) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetKeyPolicyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse)value; Amazon.KeyManagementService.Model.GetKeyPolicyResponse converted = new Amazon.KeyManagementService.Model.GetKeyPolicyResponse(); if (concrete._Policy.is_Some) converted.Policy = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(concrete._Policy); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse (Amazon.KeyManagementService.Model.GetKeyPolicyResponse value) {
 string var_policy = value.Policy;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(var_policy) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest)value; Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest converted = new Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(concrete._KeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest (Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(value.KeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse)value; Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse converted = new Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse(); if (concrete._KeyRotationEnabled.is_Some) converted.KeyRotationEnabled = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(concrete._KeyRotationEnabled); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse (Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse value) {
 bool? var_keyRotationEnabled = value.KeyRotationEnabled;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(var_keyRotationEnabled) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetParametersForImportRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest)value; Amazon.KeyManagementService.Model.GetParametersForImportRequest converted = new Amazon.KeyManagementService.Model.GetParametersForImportRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(concrete._KeyId);
  converted.WrappingAlgorithm = (Amazon.KeyManagementService.AlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(concrete._WrappingAlgorithm);
  converted.WrappingKeySpec = (Amazon.KeyManagementService.WrappingKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(concrete._WrappingKeySpec); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest (Amazon.KeyManagementService.Model.GetParametersForImportRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(value.WrappingAlgorithm) , ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(value.WrappingKeySpec) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetParametersForImportResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse)value; Amazon.KeyManagementService.Model.GetParametersForImportResponse converted = new Amazon.KeyManagementService.Model.GetParametersForImportResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(concrete._KeyId);
 if (concrete._ImportToken.is_Some) converted.ImportToken = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(concrete._ImportToken);
 if (concrete._PublicKey.is_Some) converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(concrete._PublicKey);
 if (concrete._ParametersValidTo.is_Some) converted.ParametersValidTo = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(concrete._ParametersValidTo); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse (Amazon.KeyManagementService.Model.GetParametersForImportResponse value) {
 string var_keyId = value.KeyId;
 System.IO.MemoryStream var_importToken = value.ImportToken;
 System.IO.MemoryStream var_publicKey = value.PublicKey;
 System.DateTime? var_parametersValidTo = value.ParametersValidTo;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(var_importToken) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(var_publicKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(var_parametersValidTo) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetPublicKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest)value; Amazon.KeyManagementService.Model.GetPublicKeyRequest converted = new Amazon.KeyManagementService.Model.GetPublicKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(concrete._KeyId);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest (Amazon.KeyManagementService.Model.GetPublicKeyRequest value) {
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.GetPublicKeyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse)value; Amazon.KeyManagementService.Model.GetPublicKeyResponse converted = new Amazon.KeyManagementService.Model.GetPublicKeyResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(concrete._KeyId);
 if (concrete._PublicKey.is_Some) converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(concrete._PublicKey);
 if (concrete._CustomerMasterKeySpec.is_Some) converted.CustomerMasterKeySpec = (Amazon.KeyManagementService.CustomerMasterKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(concrete._CustomerMasterKeySpec);
 if (concrete._KeySpec.is_Some) converted.KeySpec = (Amazon.KeyManagementService.KeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(concrete._KeySpec);
 if (concrete._KeyUsage.is_Some) converted.KeyUsage = (Amazon.KeyManagementService.KeyUsageType) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(concrete._KeyUsage);
 if (concrete._EncryptionAlgorithms.is_Some) converted.EncryptionAlgorithms = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(concrete._EncryptionAlgorithms);
 if (concrete._SigningAlgorithms.is_Some) converted.SigningAlgorithms = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(concrete._SigningAlgorithms); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse (Amazon.KeyManagementService.Model.GetPublicKeyResponse value) {
 string var_keyId = value.KeyId;
 System.IO.MemoryStream var_publicKey = value.PublicKey;
 Amazon.KeyManagementService.CustomerMasterKeySpec var_customerMasterKeySpec = value.CustomerMasterKeySpec;
 Amazon.KeyManagementService.KeySpec var_keySpec = value.KeySpec;
 Amazon.KeyManagementService.KeyUsageType var_keyUsage = value.KeyUsage;
 System.Collections.Generic.List<string> var_encryptionAlgorithms = value.EncryptionAlgorithms;
 System.Collections.Generic.List<string> var_signingAlgorithms = value.SigningAlgorithms;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(var_publicKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(var_customerMasterKeySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(var_keySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(var_keyUsage) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(var_encryptionAlgorithms) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(var_signingAlgorithms) ) ;
}
 internal static Amazon.KeyManagementService.GrantOperation FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation (software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation value) {
 if (value.is_Decrypt) return Amazon.KeyManagementService.GrantOperation.Decrypt;
 if (value.is_Encrypt) return Amazon.KeyManagementService.GrantOperation.Encrypt;
 if (value.is_GenerateDataKey) return Amazon.KeyManagementService.GrantOperation.GenerateDataKey;
 if (value.is_GenerateDataKeyWithoutPlaintext) return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyWithoutPlaintext;
 if (value.is_ReEncryptFrom) return Amazon.KeyManagementService.GrantOperation.ReEncryptFrom;
 if (value.is_ReEncryptTo) return Amazon.KeyManagementService.GrantOperation.ReEncryptTo;
 if (value.is_Sign) return Amazon.KeyManagementService.GrantOperation.Sign;
 if (value.is_Verify) return Amazon.KeyManagementService.GrantOperation.Verify;
 if (value.is_GetPublicKey) return Amazon.KeyManagementService.GrantOperation.GetPublicKey;
 if (value.is_CreateGrant) return Amazon.KeyManagementService.GrantOperation.CreateGrant;
 if (value.is_RetireGrant) return Amazon.KeyManagementService.GrantOperation.RetireGrant;
 if (value.is_DescribeKey) return Amazon.KeyManagementService.GrantOperation.DescribeKey;
 if (value.is_GenerateDataKeyPair) return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPair;
 if (value.is_GenerateDataKeyPairWithoutPlaintext) return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPairWithoutPlaintext;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.GrantOperation value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation (Amazon.KeyManagementService.GrantOperation value) {
 if (Amazon.KeyManagementService.GrantOperation.Decrypt.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_Decrypt();
 if (Amazon.KeyManagementService.GrantOperation.Encrypt.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_Encrypt();
 if (Amazon.KeyManagementService.GrantOperation.GenerateDataKey.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_GenerateDataKey();
 if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyWithoutPlaintext.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_GenerateDataKeyWithoutPlaintext();
 if (Amazon.KeyManagementService.GrantOperation.ReEncryptFrom.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_ReEncryptFrom();
 if (Amazon.KeyManagementService.GrantOperation.ReEncryptTo.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_ReEncryptTo();
 if (Amazon.KeyManagementService.GrantOperation.Sign.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_Sign();
 if (Amazon.KeyManagementService.GrantOperation.Verify.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_Verify();
 if (Amazon.KeyManagementService.GrantOperation.GetPublicKey.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_GetPublicKey();
 if (Amazon.KeyManagementService.GrantOperation.CreateGrant.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_CreateGrant();
 if (Amazon.KeyManagementService.GrantOperation.RetireGrant.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_RetireGrant();
 if (Amazon.KeyManagementService.GrantOperation.DescribeKey.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_DescribeKey();
 if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPair.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_GenerateDataKeyPair();
 if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPairWithoutPlaintext.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.create_GenerateDataKeyPairWithoutPlaintext();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.GrantOperation value");
}
 internal static Amazon.KeyManagementService.Model.ImportKeyMaterialRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest (software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest)value; Amazon.KeyManagementService.Model.ImportKeyMaterialRequest converted = new Amazon.KeyManagementService.Model.ImportKeyMaterialRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(concrete._KeyId);
  converted.ImportToken = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(concrete._ImportToken);
  converted.EncryptedKeyMaterial = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(concrete._EncryptedKeyMaterial);
 if (concrete._ValidTo.is_Some) converted.ValidTo = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(concrete._ValidTo);
 if (concrete._ExpirationModel.is_Some) converted.ExpirationModel = (Amazon.KeyManagementService.ExpirationModelType) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(concrete._ExpirationModel); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest (Amazon.KeyManagementService.Model.ImportKeyMaterialRequest value) {
 System.DateTime? var_validTo = value.ValidTo;
 Amazon.KeyManagementService.ExpirationModelType var_expirationModel = value.ExpirationModel;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(value.ImportToken) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(value.EncryptedKeyMaterial) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(var_validTo) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(var_expirationModel) ) ;
}
 internal static Amazon.KeyManagementService.Model.ImportKeyMaterialResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse (software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse)value; Amazon.KeyManagementService.Model.ImportKeyMaterialResponse converted = new Amazon.KeyManagementService.Model.ImportKeyMaterialResponse();  return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse (Amazon.KeyManagementService.Model.ImportKeyMaterialResponse value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse (  ) ;
}
 internal static Amazon.KeyManagementService.Model.IncorrectKeyException FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException (software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException value) {
 return new Amazon.KeyManagementService.Model.IncorrectKeyException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException (Amazon.KeyManagementService.Model.IncorrectKeyException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.IncorrectKeyMaterialException FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException (software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException value) {
 return new Amazon.KeyManagementService.Model.IncorrectKeyMaterialException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException (Amazon.KeyManagementService.Model.IncorrectKeyMaterialException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.IncorrectTrustAnchorException FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException (software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException value) {
 return new Amazon.KeyManagementService.Model.IncorrectTrustAnchorException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException (Amazon.KeyManagementService.Model.IncorrectTrustAnchorException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidAliasNameException FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException value) {
 return new Amazon.KeyManagementService.Model.InvalidAliasNameException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException (Amazon.KeyManagementService.Model.InvalidAliasNameException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidArnException FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException value) {
 return new Amazon.KeyManagementService.Model.InvalidArnException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException (Amazon.KeyManagementService.Model.InvalidArnException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidCiphertextException FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException value) {
 return new Amazon.KeyManagementService.Model.InvalidCiphertextException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException (Amazon.KeyManagementService.Model.InvalidCiphertextException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidGrantIdException FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException value) {
 return new Amazon.KeyManagementService.Model.InvalidGrantIdException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException (Amazon.KeyManagementService.Model.InvalidGrantIdException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidGrantTokenException FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException value) {
 return new Amazon.KeyManagementService.Model.InvalidGrantTokenException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException (Amazon.KeyManagementService.Model.InvalidGrantTokenException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidImportTokenException FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException value) {
 return new Amazon.KeyManagementService.Model.InvalidImportTokenException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException (Amazon.KeyManagementService.Model.InvalidImportTokenException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidKeyUsageException FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException value) {
 return new Amazon.KeyManagementService.Model.InvalidKeyUsageException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException (Amazon.KeyManagementService.Model.InvalidKeyUsageException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.InvalidMarkerException FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException (software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException value) {
 return new Amazon.KeyManagementService.Model.InvalidMarkerException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException (Amazon.KeyManagementService.Model.InvalidMarkerException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.KeyManagerType FromDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType (software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType value) {
 if (value.is_AWS) return Amazon.KeyManagementService.KeyManagerType.AWS;
 if (value.is_CUSTOMER) return Amazon.KeyManagementService.KeyManagerType.CUSTOMER;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyManagerType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType ToDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType (Amazon.KeyManagementService.KeyManagerType value) {
 if (Amazon.KeyManagementService.KeyManagerType.AWS.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType.create_AWS();
 if (Amazon.KeyManagementService.KeyManagerType.CUSTOMER.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType.create_CUSTOMER();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyManagerType value");
}
 internal static Amazon.KeyManagementService.KeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec (software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec value) {
 if (value.is_RSA__2048) return Amazon.KeyManagementService.KeySpec.RSA_2048;
 if (value.is_RSA__3072) return Amazon.KeyManagementService.KeySpec.RSA_3072;
 if (value.is_RSA__4096) return Amazon.KeyManagementService.KeySpec.RSA_4096;
 if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P256;
 if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P384;
 if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P521;
 if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.KeySpec.ECC_SECG_P256K1;
 if (value.is_SYMMETRIC__DEFAULT) return Amazon.KeyManagementService.KeySpec.SYMMETRIC_DEFAULT;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeySpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec (Amazon.KeyManagementService.KeySpec value) {
 if (Amazon.KeyManagementService.KeySpec.RSA_2048.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_RSA__2048();
 if (Amazon.KeyManagementService.KeySpec.RSA_3072.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_RSA__3072();
 if (Amazon.KeyManagementService.KeySpec.RSA_4096.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_RSA__4096();
 if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_ECC__NIST__P256();
 if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_ECC__NIST__P384();
 if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P521.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_ECC__NIST__P521();
 if (Amazon.KeyManagementService.KeySpec.ECC_SECG_P256K1.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_ECC__SECG__P256K1();
 if (Amazon.KeyManagementService.KeySpec.SYMMETRIC_DEFAULT.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.create_SYMMETRIC__DEFAULT();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeySpec value");
}
 internal static Amazon.KeyManagementService.KeyState FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState (software.amazon.cryptography.services.kms.internaldafny.types._IKeyState value) {
 if (value.is_Creating) return Amazon.KeyManagementService.KeyState.Creating;
 if (value.is_Enabled) return Amazon.KeyManagementService.KeyState.Enabled;
 if (value.is_Disabled) return Amazon.KeyManagementService.KeyState.Disabled;
 if (value.is_PendingDeletion) return Amazon.KeyManagementService.KeyState.PendingDeletion;
 if (value.is_PendingImport) return Amazon.KeyManagementService.KeyState.PendingImport;
 if (value.is_PendingReplicaDeletion) return Amazon.KeyManagementService.KeyState.PendingReplicaDeletion;
 if (value.is_Unavailable) return Amazon.KeyManagementService.KeyState.Unavailable;
 if (value.is_Updating) return Amazon.KeyManagementService.KeyState.Updating;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyState value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IKeyState ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState (Amazon.KeyManagementService.KeyState value) {
 if (Amazon.KeyManagementService.KeyState.Creating.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_Creating();
 if (Amazon.KeyManagementService.KeyState.Enabled.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_Enabled();
 if (Amazon.KeyManagementService.KeyState.Disabled.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_Disabled();
 if (Amazon.KeyManagementService.KeyState.PendingDeletion.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_PendingDeletion();
 if (Amazon.KeyManagementService.KeyState.PendingImport.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_PendingImport();
 if (Amazon.KeyManagementService.KeyState.PendingReplicaDeletion.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_PendingReplicaDeletion();
 if (Amazon.KeyManagementService.KeyState.Unavailable.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_Unavailable();
 if (Amazon.KeyManagementService.KeyState.Updating.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyState.create_Updating();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyState value");
}
 internal static Amazon.KeyManagementService.Model.KeyUnavailableException FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException (software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException value) {
 return new Amazon.KeyManagementService.Model.KeyUnavailableException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException (Amazon.KeyManagementService.Model.KeyUnavailableException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.KeyUsageType FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType (software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType value) {
 if (value.is_SIGN__VERIFY) return Amazon.KeyManagementService.KeyUsageType.SIGN_VERIFY;
 if (value.is_ENCRYPT__DECRYPT) return Amazon.KeyManagementService.KeyUsageType.ENCRYPT_DECRYPT;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyUsageType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType (Amazon.KeyManagementService.KeyUsageType value) {
 if (Amazon.KeyManagementService.KeyUsageType.SIGN_VERIFY.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.create_SIGN__VERIFY();
 if (Amazon.KeyManagementService.KeyUsageType.ENCRYPT_DECRYPT.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.create_ENCRYPT__DECRYPT();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyUsageType value");
}
 internal static Amazon.KeyManagementService.Model.KMSInternalException FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException (software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException value) {
 return new Amazon.KeyManagementService.Model.KMSInternalException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException (Amazon.KeyManagementService.Model.KMSInternalException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.KMSInvalidSignatureException FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException (software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException value) {
 return new Amazon.KeyManagementService.Model.KMSInvalidSignatureException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException (Amazon.KeyManagementService.Model.KMSInvalidSignatureException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.KMSInvalidStateException FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException (software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException value) {
 return new Amazon.KeyManagementService.Model.KMSInvalidStateException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException (Amazon.KeyManagementService.Model.KMSInvalidStateException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.LimitExceededException FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException (software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException value) {
 return new Amazon.KeyManagementService.Model.LimitExceededException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException (Amazon.KeyManagementService.Model.LimitExceededException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.ListAliasesRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest (software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest)value; Amazon.KeyManagementService.Model.ListAliasesRequest converted = new Amazon.KeyManagementService.Model.ListAliasesRequest(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(concrete._KeyId);
 if (concrete._Limit.is_Some) converted.Limit = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(concrete._Limit);
 if (concrete._Marker.is_Some) converted.Marker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(concrete._Marker); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest (Amazon.KeyManagementService.Model.ListAliasesRequest value) {
 string var_keyId = value.KeyId;
 int? var_limit = value.Limit;
 string var_marker = value.Marker;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(var_limit) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(var_marker) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListAliasesResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse (software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse)value; Amazon.KeyManagementService.Model.ListAliasesResponse converted = new Amazon.KeyManagementService.Model.ListAliasesResponse(); if (concrete._Aliases.is_Some) converted.Aliases = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(concrete._Aliases);
 if (concrete._NextMarker.is_Some) converted.NextMarker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(concrete._NextMarker);
 if (concrete._Truncated.is_Some) converted.Truncated = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(concrete._Truncated); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse (Amazon.KeyManagementService.Model.ListAliasesResponse value) {
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> var_aliases = value.Aliases;
 string var_nextMarker = value.NextMarker;
 bool? var_truncated = value.Truncated;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(var_aliases) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(var_nextMarker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(var_truncated) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListGrantsRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest (software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest)value; Amazon.KeyManagementService.Model.ListGrantsRequest converted = new Amazon.KeyManagementService.Model.ListGrantsRequest(); if (concrete._Limit.is_Some) converted.Limit = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(concrete._Limit);
 if (concrete._Marker.is_Some) converted.Marker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(concrete._Marker);
  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(concrete._KeyId);
 if (concrete._GrantId.is_Some) converted.GrantId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(concrete._GrantId);
 if (concrete._GranteePrincipal.is_Some) converted.GranteePrincipal = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(concrete._GranteePrincipal); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest (Amazon.KeyManagementService.Model.ListGrantsRequest value) {
 int? var_limit = value.Limit;
 string var_marker = value.Marker;
 string var_grantId = value.GrantId;
 string var_granteePrincipal = value.GranteePrincipal;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(var_limit) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(var_marker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(var_grantId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(var_granteePrincipal) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListGrantsResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse (software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse)value; Amazon.KeyManagementService.Model.ListGrantsResponse converted = new Amazon.KeyManagementService.Model.ListGrantsResponse(); if (concrete._Grants.is_Some) converted.Grants = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(concrete._Grants);
 if (concrete._NextMarker.is_Some) converted.NextMarker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(concrete._NextMarker);
 if (concrete._Truncated.is_Some) converted.Truncated = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(concrete._Truncated); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse (Amazon.KeyManagementService.Model.ListGrantsResponse value) {
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> var_grants = value.Grants;
 string var_nextMarker = value.NextMarker;
 bool? var_truncated = value.Truncated;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(var_grants) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(var_nextMarker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(var_truncated) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListKeyPoliciesRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest (software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest)value; Amazon.KeyManagementService.Model.ListKeyPoliciesRequest converted = new Amazon.KeyManagementService.Model.ListKeyPoliciesRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(concrete._KeyId);
 if (concrete._Limit.is_Some) converted.Limit = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(concrete._Limit);
 if (concrete._Marker.is_Some) converted.Marker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(concrete._Marker); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest (Amazon.KeyManagementService.Model.ListKeyPoliciesRequest value) {
 int? var_limit = value.Limit;
 string var_marker = value.Marker;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(var_limit) , ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(var_marker) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListKeyPoliciesResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse (software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse)value; Amazon.KeyManagementService.Model.ListKeyPoliciesResponse converted = new Amazon.KeyManagementService.Model.ListKeyPoliciesResponse(); if (concrete._PolicyNames.is_Some) converted.PolicyNames = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(concrete._PolicyNames);
 if (concrete._NextMarker.is_Some) converted.NextMarker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(concrete._NextMarker);
 if (concrete._Truncated.is_Some) converted.Truncated = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(concrete._Truncated); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse (Amazon.KeyManagementService.Model.ListKeyPoliciesResponse value) {
 System.Collections.Generic.List<string> var_policyNames = value.PolicyNames;
 string var_nextMarker = value.NextMarker;
 bool? var_truncated = value.Truncated;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(var_policyNames) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(var_nextMarker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(var_truncated) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListResourceTagsRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest (software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest)value; Amazon.KeyManagementService.Model.ListResourceTagsRequest converted = new Amazon.KeyManagementService.Model.ListResourceTagsRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(concrete._KeyId);
 if (concrete._Limit.is_Some) converted.Limit = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(concrete._Limit);
 if (concrete._Marker.is_Some) converted.Marker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(concrete._Marker); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest (Amazon.KeyManagementService.Model.ListResourceTagsRequest value) {
 int? var_limit = value.Limit;
 string var_marker = value.Marker;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(var_limit) , ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(var_marker) ) ;
}
 internal static Amazon.KeyManagementService.Model.ListResourceTagsResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse (software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse)value; Amazon.KeyManagementService.Model.ListResourceTagsResponse converted = new Amazon.KeyManagementService.Model.ListResourceTagsResponse(); if (concrete._Tags.is_Some) converted.Tags = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(concrete._Tags);
 if (concrete._NextMarker.is_Some) converted.NextMarker = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(concrete._NextMarker);
 if (concrete._Truncated.is_Some) converted.Truncated = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(concrete._Truncated); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse (Amazon.KeyManagementService.Model.ListResourceTagsResponse value) {
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> var_tags = value.Tags;
 string var_nextMarker = value.NextMarker;
 bool? var_truncated = value.Truncated;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(var_tags) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(var_nextMarker) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(var_truncated) ) ;
}
 internal static Amazon.KeyManagementService.Model.MalformedPolicyDocumentException FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException (software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException value) {
 return new Amazon.KeyManagementService.Model.MalformedPolicyDocumentException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException (Amazon.KeyManagementService.Model.MalformedPolicyDocumentException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.MessageType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType (software.amazon.cryptography.services.kms.internaldafny.types._IMessageType value) {
 if (value.is_RAW) return Amazon.KeyManagementService.MessageType.RAW;
 if (value.is_DIGEST) return Amazon.KeyManagementService.MessageType.DIGEST;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MessageType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IMessageType ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType (Amazon.KeyManagementService.MessageType value) {
 if (Amazon.KeyManagementService.MessageType.RAW.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.MessageType.create_RAW();
 if (Amazon.KeyManagementService.MessageType.DIGEST.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.MessageType.create_DIGEST();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MessageType value");
}
 internal static Amazon.KeyManagementService.MultiRegionKeyType FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType (software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType value) {
 if (value.is_PRIMARY) return Amazon.KeyManagementService.MultiRegionKeyType.PRIMARY;
 if (value.is_REPLICA) return Amazon.KeyManagementService.MultiRegionKeyType.REPLICA;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MultiRegionKeyType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType (Amazon.KeyManagementService.MultiRegionKeyType value) {
 if (Amazon.KeyManagementService.MultiRegionKeyType.PRIMARY.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType.create_PRIMARY();
 if (Amazon.KeyManagementService.MultiRegionKeyType.REPLICA.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType.create_REPLICA();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MultiRegionKeyType value");
}
 internal static Amazon.KeyManagementService.Model.NotFoundException FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException (software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException value) {
 return new Amazon.KeyManagementService.Model.NotFoundException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException (Amazon.KeyManagementService.Model.NotFoundException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.OriginType FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType (software.amazon.cryptography.services.kms.internaldafny.types._IOriginType value) {
 if (value.is_AWS__KMS) return Amazon.KeyManagementService.OriginType.AWS_KMS;
 if (value.is_EXTERNAL) return Amazon.KeyManagementService.OriginType.EXTERNAL;
 if (value.is_AWS__CLOUDHSM) return Amazon.KeyManagementService.OriginType.AWS_CLOUDHSM;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.OriginType value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IOriginType ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType (Amazon.KeyManagementService.OriginType value) {
 if (Amazon.KeyManagementService.OriginType.AWS_KMS.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.OriginType.create_AWS__KMS();
 if (Amazon.KeyManagementService.OriginType.EXTERNAL.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.OriginType.create_EXTERNAL();
 if (Amazon.KeyManagementService.OriginType.AWS_CLOUDHSM.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.OriginType.create_AWS__CLOUDHSM();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.OriginType value");
}
 internal static Amazon.KeyManagementService.Model.PutKeyPolicyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest)value; Amazon.KeyManagementService.Model.PutKeyPolicyRequest converted = new Amazon.KeyManagementService.Model.PutKeyPolicyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(concrete._KeyId);
  converted.PolicyName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(concrete._PolicyName);
  converted.Policy = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(concrete._Policy);
 if (concrete._BypassPolicyLockoutSafetyCheck.is_Some) converted.BypassPolicyLockoutSafetyCheck = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(concrete._BypassPolicyLockoutSafetyCheck); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest (Amazon.KeyManagementService.Model.PutKeyPolicyRequest value) {
 bool? var_bypassPolicyLockoutSafetyCheck = value.BypassPolicyLockoutSafetyCheck;
 return new software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(value.PolicyName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(value.Policy) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(var_bypassPolicyLockoutSafetyCheck) ) ;
}
 internal static Amazon.KeyManagementService.Model.ReEncryptRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest (software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest)value; Amazon.KeyManagementService.Model.ReEncryptRequest converted = new Amazon.KeyManagementService.Model.ReEncryptRequest();  converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._SourceEncryptionContext.is_Some) converted.SourceEncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(concrete._SourceEncryptionContext);
 if (concrete._SourceKeyId.is_Some) converted.SourceKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(concrete._SourceKeyId);
  converted.DestinationKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(concrete._DestinationKeyId);
 if (concrete._DestinationEncryptionContext.is_Some) converted.DestinationEncryptionContext = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(concrete._DestinationEncryptionContext);
 if (concrete._SourceEncryptionAlgorithm.is_Some) converted.SourceEncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(concrete._SourceEncryptionAlgorithm);
 if (concrete._DestinationEncryptionAlgorithm.is_Some) converted.DestinationEncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(concrete._DestinationEncryptionAlgorithm);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest (Amazon.KeyManagementService.Model.ReEncryptRequest value) {
 System.Collections.Generic.Dictionary<string, string> var_sourceEncryptionContext = value.SourceEncryptionContext;
 string var_sourceKeyId = value.SourceKeyId;
 System.Collections.Generic.Dictionary<string, string> var_destinationEncryptionContext = value.DestinationEncryptionContext;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_sourceEncryptionAlgorithm = value.SourceEncryptionAlgorithm;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_destinationEncryptionAlgorithm = value.DestinationEncryptionAlgorithm;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(value.CiphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(var_sourceEncryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(var_sourceKeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(value.DestinationKeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(var_destinationEncryptionContext) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(var_sourceEncryptionAlgorithm) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(var_destinationEncryptionAlgorithm) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.ReEncryptResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse (software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse)value; Amazon.KeyManagementService.Model.ReEncryptResponse converted = new Amazon.KeyManagementService.Model.ReEncryptResponse(); if (concrete._CiphertextBlob.is_Some) converted.CiphertextBlob = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(concrete._CiphertextBlob);
 if (concrete._SourceKeyId.is_Some) converted.SourceKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(concrete._SourceKeyId);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(concrete._KeyId);
 if (concrete._SourceEncryptionAlgorithm.is_Some) converted.SourceEncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(concrete._SourceEncryptionAlgorithm);
 if (concrete._DestinationEncryptionAlgorithm.is_Some) converted.DestinationEncryptionAlgorithm = (Amazon.KeyManagementService.EncryptionAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(concrete._DestinationEncryptionAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse (Amazon.KeyManagementService.Model.ReEncryptResponse value) {
 System.IO.MemoryStream var_ciphertextBlob = value.CiphertextBlob;
 string var_sourceKeyId = value.SourceKeyId;
 string var_keyId = value.KeyId;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_sourceEncryptionAlgorithm = value.SourceEncryptionAlgorithm;
 Amazon.KeyManagementService.EncryptionAlgorithmSpec var_destinationEncryptionAlgorithm = value.DestinationEncryptionAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(var_ciphertextBlob) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(var_sourceKeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(var_sourceEncryptionAlgorithm) , ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(var_destinationEncryptionAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.ReplicateKeyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest)value; Amazon.KeyManagementService.Model.ReplicateKeyRequest converted = new Amazon.KeyManagementService.Model.ReplicateKeyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(concrete._KeyId);
  converted.ReplicaRegion = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(concrete._ReplicaRegion);
 if (concrete._Policy.is_Some) converted.Policy = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(concrete._Policy);
 if (concrete._BypassPolicyLockoutSafetyCheck.is_Some) converted.BypassPolicyLockoutSafetyCheck = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(concrete._BypassPolicyLockoutSafetyCheck);
 if (concrete._Description.is_Some) converted.Description = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(concrete._Description);
 if (concrete._Tags.is_Some) converted.Tags = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(concrete._Tags); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest (Amazon.KeyManagementService.Model.ReplicateKeyRequest value) {
 string var_policy = value.Policy;
 bool? var_bypassPolicyLockoutSafetyCheck = value.BypassPolicyLockoutSafetyCheck;
 string var_description = value.Description;
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> var_tags = value.Tags;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(value.ReplicaRegion) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(var_policy) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(var_bypassPolicyLockoutSafetyCheck) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(var_description) , ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(var_tags) ) ;
}
 internal static Amazon.KeyManagementService.Model.ReplicateKeyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse)value; Amazon.KeyManagementService.Model.ReplicateKeyResponse converted = new Amazon.KeyManagementService.Model.ReplicateKeyResponse(); if (concrete._ReplicaKeyMetadata.is_Some) converted.ReplicaKeyMetadata = (Amazon.KeyManagementService.Model.KeyMetadata) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(concrete._ReplicaKeyMetadata);
 if (concrete._ReplicaPolicy.is_Some) converted.ReplicaPolicy = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(concrete._ReplicaPolicy);
 if (concrete._ReplicaTags.is_Some) converted.ReplicaTags = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(concrete._ReplicaTags); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse (Amazon.KeyManagementService.Model.ReplicateKeyResponse value) {
 Amazon.KeyManagementService.Model.KeyMetadata var_replicaKeyMetadata = value.ReplicaKeyMetadata;
 string var_replicaPolicy = value.ReplicaPolicy;
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> var_replicaTags = value.ReplicaTags;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(var_replicaKeyMetadata) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(var_replicaPolicy) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(var_replicaTags) ) ;
}
 internal static Amazon.KeyManagementService.Model.RetireGrantRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest (software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest)value; Amazon.KeyManagementService.Model.RetireGrantRequest converted = new Amazon.KeyManagementService.Model.RetireGrantRequest(); if (concrete._GrantToken.is_Some) converted.GrantToken = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(concrete._GrantToken);
 if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(concrete._KeyId);
 if (concrete._GrantId.is_Some) converted.GrantId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(concrete._GrantId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest (Amazon.KeyManagementService.Model.RetireGrantRequest value) {
 string var_grantToken = value.GrantToken;
 string var_keyId = value.KeyId;
 string var_grantId = value.GrantId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(var_grantToken) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(var_grantId) ) ;
}
 internal static Amazon.KeyManagementService.Model.RevokeGrantRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest (software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest)value; Amazon.KeyManagementService.Model.RevokeGrantRequest converted = new Amazon.KeyManagementService.Model.RevokeGrantRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(concrete._KeyId);
  converted.GrantId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(concrete._GrantId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest (Amazon.KeyManagementService.Model.RevokeGrantRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(value.GrantId) ) ;
}
 internal static Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest (software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest)value; Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest converted = new Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(concrete._KeyId);
 if (concrete._PendingWindowInDays.is_Some) converted.PendingWindowInDays = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(concrete._PendingWindowInDays); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest (Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest value) {
 int? var_pendingWindowInDays = value.PendingWindowInDays;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(var_pendingWindowInDays) ) ;
}
 internal static Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse (software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse)value; Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse converted = new Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(concrete._KeyId);
 if (concrete._DeletionDate.is_Some) converted.DeletionDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(concrete._DeletionDate);
 if (concrete._KeyState.is_Some) converted.KeyState = (Amazon.KeyManagementService.KeyState) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(concrete._KeyState);
 if (concrete._PendingWindowInDays.is_Some) converted.PendingWindowInDays = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(concrete._PendingWindowInDays); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse (Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse value) {
 string var_keyId = value.KeyId;
 System.DateTime? var_deletionDate = value.DeletionDate;
 Amazon.KeyManagementService.KeyState var_keyState = value.KeyState;
 int? var_pendingWindowInDays = value.PendingWindowInDays;
 return new software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(var_deletionDate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(var_keyState) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(var_pendingWindowInDays) ) ;
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec (software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec value) {
 if (value.is_RSASSA__PSS__SHA__256) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_256;
 if (value.is_RSASSA__PSS__SHA__384) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_384;
 if (value.is_RSASSA__PSS__SHA__512) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_512;
 if (value.is_RSASSA__PKCS1__V1__5__SHA__256) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256;
 if (value.is_RSASSA__PKCS1__V1__5__SHA__384) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384;
 if (value.is_RSASSA__PKCS1__V1__5__SHA__512) return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512;
 if (value.is_ECDSA__SHA__256) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_256;
 if (value.is_ECDSA__SHA__384) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_384;
 if (value.is_ECDSA__SHA__512) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_512;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.SigningAlgorithmSpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__256();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__384();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_512.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__512();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__256();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__384();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__512();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_256.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_ECDSA__SHA__256();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_384.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_ECDSA__SHA__384();
 if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_512.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.create_ECDSA__SHA__512();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.SigningAlgorithmSpec value");
}
 internal static Amazon.KeyManagementService.Model.SignRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest (software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.SignRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.SignRequest)value; Amazon.KeyManagementService.Model.SignRequest converted = new Amazon.KeyManagementService.Model.SignRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(concrete._KeyId);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(concrete._Message);
 if (concrete._MessageType.is_Some) converted.MessageType = (Amazon.KeyManagementService.MessageType) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(concrete._MessageType);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(concrete._GrantTokens);
  converted.SigningAlgorithm = (Amazon.KeyManagementService.SigningAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(concrete._SigningAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest (Amazon.KeyManagementService.Model.SignRequest value) {
 Amazon.KeyManagementService.MessageType var_messageType = value.MessageType;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.SignRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(value.Message) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(var_messageType) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(var_grantTokens) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(value.SigningAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.SignResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse (software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.SignResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.SignResponse)value; Amazon.KeyManagementService.Model.SignResponse converted = new Amazon.KeyManagementService.Model.SignResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(concrete._KeyId);
 if (concrete._Signature.is_Some) converted.Signature = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(concrete._Signature);
 if (concrete._SigningAlgorithm.is_Some) converted.SigningAlgorithm = (Amazon.KeyManagementService.SigningAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(concrete._SigningAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse (Amazon.KeyManagementService.Model.SignResponse value) {
 string var_keyId = value.KeyId;
 System.IO.MemoryStream var_signature = value.Signature;
 Amazon.KeyManagementService.SigningAlgorithmSpec var_signingAlgorithm = value.SigningAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.SignResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(var_signature) , ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(var_signingAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.Model.TagException FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException (software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException value) {
 return new Amazon.KeyManagementService.Model.TagException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException (Amazon.KeyManagementService.Model.TagException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.TagResourceRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest (software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest)value; Amazon.KeyManagementService.Model.TagResourceRequest converted = new Amazon.KeyManagementService.Model.TagResourceRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(concrete._KeyId);
  converted.Tags = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(concrete._Tags); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest (Amazon.KeyManagementService.Model.TagResourceRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(value.Tags) ) ;
}
 internal static Amazon.KeyManagementService.Model.UnsupportedOperationException FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException (software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException value) {
 return new Amazon.KeyManagementService.Model.UnsupportedOperationException (
 FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException (Amazon.KeyManagementService.Model.UnsupportedOperationException value) {
 string var_message = value.Message;
 return new software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException (
 ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message(var_message)
 ) ;
}
 internal static Amazon.KeyManagementService.Model.UntagResourceRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest (software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest)value; Amazon.KeyManagementService.Model.UntagResourceRequest converted = new Amazon.KeyManagementService.Model.UntagResourceRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(concrete._KeyId);
  converted.TagKeys = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(concrete._TagKeys); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest (Amazon.KeyManagementService.Model.UntagResourceRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(value.TagKeys) ) ;
}
 internal static Amazon.KeyManagementService.Model.UpdateAliasRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest (software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest)value; Amazon.KeyManagementService.Model.UpdateAliasRequest converted = new Amazon.KeyManagementService.Model.UpdateAliasRequest();  converted.AliasName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(concrete._AliasName);
  converted.TargetKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(concrete._TargetKeyId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest (Amazon.KeyManagementService.Model.UpdateAliasRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(value.AliasName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(value.TargetKeyId) ) ;
}
 internal static Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest (software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest)value; Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest converted = new Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest();  converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(concrete._CustomKeyStoreId);
 if (concrete._NewCustomKeyStoreName.is_Some) converted.NewCustomKeyStoreName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(concrete._NewCustomKeyStoreName);
 if (concrete._KeyStorePassword.is_Some) converted.KeyStorePassword = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(concrete._KeyStorePassword);
 if (concrete._CloudHsmClusterId.is_Some) converted.CloudHsmClusterId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(concrete._CloudHsmClusterId); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest (Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest value) {
 string var_newCustomKeyStoreName = value.NewCustomKeyStoreName;
 string var_keyStorePassword = value.KeyStorePassword;
 string var_cloudHsmClusterId = value.CloudHsmClusterId;
 return new software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(value.CustomKeyStoreId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(var_newCustomKeyStoreName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(var_keyStorePassword) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(var_cloudHsmClusterId) ) ;
}
 internal static Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse (software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse)value; Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse converted = new Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse();  return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse (Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse (  ) ;
}
 internal static Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest (software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest)value; Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest converted = new Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(concrete._KeyId);
  converted.Description = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(concrete._Description); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest (Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(value.Description) ) ;
}
 internal static Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest (software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest)value; Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest converted = new Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(concrete._KeyId);
  converted.PrimaryRegion = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(concrete._PrimaryRegion); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest (Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(value.PrimaryRegion) ) ;
}
 internal static Amazon.KeyManagementService.Model.VerifyRequest FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest (software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest value) {
 software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest concrete = (software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest)value; Amazon.KeyManagementService.Model.VerifyRequest converted = new Amazon.KeyManagementService.Model.VerifyRequest();  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(concrete._KeyId);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(concrete._Message);
 if (concrete._MessageType.is_Some) converted.MessageType = (Amazon.KeyManagementService.MessageType) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(concrete._MessageType);
  converted.Signature = (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(concrete._Signature);
  converted.SigningAlgorithm = (Amazon.KeyManagementService.SigningAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(concrete._SigningAlgorithm);
 if (concrete._GrantTokens.is_Some) converted.GrantTokens = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(concrete._GrantTokens); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest (Amazon.KeyManagementService.Model.VerifyRequest value) {
 Amazon.KeyManagementService.MessageType var_messageType = value.MessageType;
 System.Collections.Generic.List<string> var_grantTokens = value.GrantTokens;
 return new software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest ( ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(value.Message) , ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(var_messageType) , ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(value.Signature) , ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(value.SigningAlgorithm) , ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(var_grantTokens) ) ;
}
 internal static Amazon.KeyManagementService.Model.VerifyResponse FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse (software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse value) {
 software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse concrete = (software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse)value; Amazon.KeyManagementService.Model.VerifyResponse converted = new Amazon.KeyManagementService.Model.VerifyResponse(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(concrete._KeyId);
 if (concrete._SignatureValid.is_Some) converted.SignatureValid = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(concrete._SignatureValid);
 if (concrete._SigningAlgorithm.is_Some) converted.SigningAlgorithm = (Amazon.KeyManagementService.SigningAlgorithmSpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(concrete._SigningAlgorithm); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse (Amazon.KeyManagementService.Model.VerifyResponse value) {
 string var_keyId = value.KeyId;
 bool? var_signatureValid = value.SignatureValid;
 Amazon.KeyManagementService.SigningAlgorithmSpec var_signingAlgorithm = value.SigningAlgorithm;
 return new software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(var_signatureValid) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(var_signingAlgorithm) ) ;
}
 internal static Amazon.KeyManagementService.WrappingKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec (software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec value) {
 if (value.is_RSA__2048) return Amazon.KeyManagementService.WrappingKeySpec.RSA_2048;
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.WrappingKeySpec value");
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec (Amazon.KeyManagementService.WrappingKeySpec value) {
 if (Amazon.KeyManagementService.WrappingKeySpec.RSA_2048.Equals(value)) return software.amazon.cryptography.services.kms.internaldafny.types.WrappingKeySpec.create();
throw new System.ArgumentException("Invalid Amazon.KeyManagementService.WrappingKeySpec value");
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value);
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations (System.Collections.Generic.List<string> value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value);
}
 internal static Amazon.KeyManagementService.Model.GrantConstraints FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.GrantConstraints) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints (Amazon.KeyManagementService.Model.GrantConstraints value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints((Amazon.KeyManagementService.Model.GrantConstraints) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
}
 internal static Amazon.KeyManagementService.KeyUsageType FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyUsageType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage (Amazon.KeyManagementService.KeyUsageType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType((Amazon.KeyManagementService.KeyUsageType) value));
}
 internal static Amazon.KeyManagementService.CustomerMasterKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec (Amazon.KeyManagementService.CustomerMasterKeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec((Amazon.KeyManagementService.CustomerMasterKeySpec) value));
}
 internal static Amazon.KeyManagementService.KeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec (Amazon.KeyManagementService.KeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
}
 internal static Amazon.KeyManagementService.OriginType FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> value) {
 return value.is_None ? (Amazon.KeyManagementService.OriginType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin (Amazon.KeyManagementService.OriginType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType((Amazon.KeyManagementService.OriginType) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType((bool) value));
}
 internal static Amazon.KeyManagementService.Model.KeyMetadata FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.KeyMetadata) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata (Amazon.KeyManagementService.Model.KeyMetadata value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata((Amazon.KeyManagementService.Model.KeyMetadata) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static Amazon.KeyManagementService.Model.KeyMetadata FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.KeyMetadata) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata (Amazon.KeyManagementService.Model.KeyMetadata value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata((Amazon.KeyManagementService.Model.KeyMetadata) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Amazon.KeyManagementService.DataKeyPairSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec (software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec (Amazon.KeyManagementService.DataKeyPairSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static Amazon.KeyManagementService.DataKeyPairSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.DataKeyPairSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec (Amazon.KeyManagementService.DataKeyPairSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec((Amazon.KeyManagementService.DataKeyPairSpec) value));
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Amazon.KeyManagementService.DataKeyPairSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec (software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec (Amazon.KeyManagementService.DataKeyPairSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static Amazon.KeyManagementService.DataKeyPairSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.DataKeyPairSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec (Amazon.KeyManagementService.DataKeyPairSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec((Amazon.KeyManagementService.DataKeyPairSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
}
 internal static Amazon.KeyManagementService.DataKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.DataKeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec (Amazon.KeyManagementService.DataKeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec((Amazon.KeyManagementService.DataKeySpec) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static Amazon.KeyManagementService.DataKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.DataKeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec (Amazon.KeyManagementService.DataKeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec((Amazon.KeyManagementService.DataKeySpec) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Amazon.KeyManagementService.AlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm (software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm (Amazon.KeyManagementService.AlgorithmSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(value);
}
 internal static Amazon.KeyManagementService.WrappingKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec (software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec (Amazon.KeyManagementService.WrappingKeySpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
}
 internal static Amazon.KeyManagementService.CustomerMasterKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec (Amazon.KeyManagementService.CustomerMasterKeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec((Amazon.KeyManagementService.CustomerMasterKeySpec) value));
}
 internal static Amazon.KeyManagementService.KeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec (Amazon.KeyManagementService.KeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
}
 internal static Amazon.KeyManagementService.KeyUsageType FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyUsageType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage (Amazon.KeyManagementService.KeyUsageType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType((Amazon.KeyManagementService.KeyUsageType) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList((System.Collections.Generic.List<string>) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static Amazon.KeyManagementService.ExpirationModelType FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> value) {
 return value.is_None ? (Amazon.KeyManagementService.ExpirationModelType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel (Amazon.KeyManagementService.ExpirationModelType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType((Amazon.KeyManagementService.ExpirationModelType) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value);
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec((Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
}
 internal static Amazon.KeyManagementService.Model.KeyMetadata FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.KeyMetadata) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata (Amazon.KeyManagementService.Model.KeyMetadata value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata((Amazon.KeyManagementService.Model.KeyMetadata) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static Amazon.KeyManagementService.KeyState FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyState) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState (Amazon.KeyManagementService.KeyState value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState((Amazon.KeyManagementService.KeyState) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static Amazon.KeyManagementService.MessageType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> value) {
 return value.is_None ? (Amazon.KeyManagementService.MessageType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType (Amazon.KeyManagementService.MessageType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType((Amazon.KeyManagementService.MessageType) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm (software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.SigningAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec((Amazon.KeyManagementService.SigningAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value);
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(value);
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys (System.Collections.Generic.List<string> value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
}
 internal static Amazon.KeyManagementService.MessageType FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> value) {
 return value.is_None ? (Amazon.KeyManagementService.MessageType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType (Amazon.KeyManagementService.MessageType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType((Amazon.KeyManagementService.MessageType) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature (Dafny.ISequence<byte> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature (System.IO.MemoryStream value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm (software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList((System.Collections.Generic.List<string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.SigningAlgorithmSpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec((Amazon.KeyManagementService.SigningAlgorithmSpec) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member).Select<Amazon.KeyManagementService.GrantOperation, string>(x => x));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>.FromArray(value.Select<string, Amazon.KeyManagementService.GrantOperation>(x => x).Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member).ToArray());
}
 internal static Amazon.KeyManagementService.Model.GrantConstraints FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints (software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints)value; Amazon.KeyManagementService.Model.GrantConstraints converted = new Amazon.KeyManagementService.Model.GrantConstraints(); if (concrete._EncryptionContextSubset.is_Some) converted.EncryptionContextSubset = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(concrete._EncryptionContextSubset);
 if (concrete._EncryptionContextEquals.is_Some) converted.EncryptionContextEquals = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(concrete._EncryptionContextEquals); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints (Amazon.KeyManagementService.Model.GrantConstraints value) {
 System.Collections.Generic.Dictionary<string, string> var_encryptionContextSubset = value.EncryptionContextSubset;
 System.Collections.Generic.Dictionary<string, string> var_encryptionContextEquals = value.EncryptionContextEquals;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints ( ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(var_encryptionContextSubset) , ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(var_encryptionContextEquals) ) ;
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member));
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member).ToArray());
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static bool FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType (bool value) {
 return value;
}
 internal static bool ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType (bool value) {
 return value;
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> value) {
 return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member).ToArray());
}
 internal static bool FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType (bool value) {
 return value;
}
 internal static bool ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType (bool value) {
 return value;
}
 internal static Amazon.KeyManagementService.Model.KeyMetadata FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata (software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata value) {
 software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata concrete = (software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata)value; Amazon.KeyManagementService.Model.KeyMetadata converted = new Amazon.KeyManagementService.Model.KeyMetadata(); if (concrete._AWSAccountId.is_Some) converted.AWSAccountId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(concrete._AWSAccountId);
  converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(concrete._KeyId);
 if (concrete._Arn.is_Some) converted.Arn = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(concrete._Arn);
 if (concrete._CreationDate.is_Some) converted.CreationDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(concrete._CreationDate);
 if (concrete._Enabled.is_Some) converted.Enabled = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(concrete._Enabled);
 if (concrete._Description.is_Some) converted.Description = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(concrete._Description);
 if (concrete._KeyUsage.is_Some) converted.KeyUsage = (Amazon.KeyManagementService.KeyUsageType) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(concrete._KeyUsage);
 if (concrete._KeyState.is_Some) converted.KeyState = (Amazon.KeyManagementService.KeyState) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(concrete._KeyState);
 if (concrete._DeletionDate.is_Some) converted.DeletionDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(concrete._DeletionDate);
 if (concrete._ValidTo.is_Some) converted.ValidTo = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(concrete._ValidTo);
 if (concrete._Origin.is_Some) converted.Origin = (Amazon.KeyManagementService.OriginType) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(concrete._Origin);
 if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(concrete._CustomKeyStoreId);
 if (concrete._CloudHsmClusterId.is_Some) converted.CloudHsmClusterId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(concrete._CloudHsmClusterId);
 if (concrete._ExpirationModel.is_Some) converted.ExpirationModel = (Amazon.KeyManagementService.ExpirationModelType) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(concrete._ExpirationModel);
 if (concrete._KeyManager.is_Some) converted.KeyManager = (Amazon.KeyManagementService.KeyManagerType) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(concrete._KeyManager);
 if (concrete._CustomerMasterKeySpec.is_Some) converted.CustomerMasterKeySpec = (Amazon.KeyManagementService.CustomerMasterKeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(concrete._CustomerMasterKeySpec);
 if (concrete._KeySpec.is_Some) converted.KeySpec = (Amazon.KeyManagementService.KeySpec) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(concrete._KeySpec);
 if (concrete._EncryptionAlgorithms.is_Some) converted.EncryptionAlgorithms = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(concrete._EncryptionAlgorithms);
 if (concrete._SigningAlgorithms.is_Some) converted.SigningAlgorithms = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(concrete._SigningAlgorithms);
 if (concrete._MultiRegion.is_Some) converted.MultiRegion = (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(concrete._MultiRegion);
 if (concrete._MultiRegionConfiguration.is_Some) converted.MultiRegionConfiguration = (Amazon.KeyManagementService.Model.MultiRegionConfiguration) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(concrete._MultiRegionConfiguration);
 if (concrete._PendingDeletionWindowInDays.is_Some) converted.PendingDeletionWindowInDays = (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(concrete._PendingDeletionWindowInDays); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata (Amazon.KeyManagementService.Model.KeyMetadata value) {
 string var_aWSAccountId = value.AWSAccountId;
 string var_arn = value.Arn;
 System.DateTime? var_creationDate = value.CreationDate;
 bool? var_enabled = value.Enabled;
 string var_description = value.Description;
 Amazon.KeyManagementService.KeyUsageType var_keyUsage = value.KeyUsage;
 Amazon.KeyManagementService.KeyState var_keyState = value.KeyState;
 System.DateTime? var_deletionDate = value.DeletionDate;
 System.DateTime? var_validTo = value.ValidTo;
 Amazon.KeyManagementService.OriginType var_origin = value.Origin;
 string var_customKeyStoreId = value.CustomKeyStoreId;
 string var_cloudHsmClusterId = value.CloudHsmClusterId;
 Amazon.KeyManagementService.ExpirationModelType var_expirationModel = value.ExpirationModel;
 Amazon.KeyManagementService.KeyManagerType var_keyManager = value.KeyManager;
 Amazon.KeyManagementService.CustomerMasterKeySpec var_customerMasterKeySpec = value.CustomerMasterKeySpec;
 Amazon.KeyManagementService.KeySpec var_keySpec = value.KeySpec;
 System.Collections.Generic.List<string> var_encryptionAlgorithms = value.EncryptionAlgorithms;
 System.Collections.Generic.List<string> var_signingAlgorithms = value.SigningAlgorithms;
 bool? var_multiRegion = value.MultiRegion;
 Amazon.KeyManagementService.Model.MultiRegionConfiguration var_multiRegionConfiguration = value.MultiRegionConfiguration;
 int? var_pendingDeletionWindowInDays = value.PendingDeletionWindowInDays;
 return new software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata ( ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(var_aWSAccountId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(value.KeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(var_arn) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(var_creationDate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(var_enabled) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(var_description) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(var_keyUsage) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(var_keyState) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(var_deletionDate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(var_validTo) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(var_origin) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(var_customKeyStoreId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(var_cloudHsmClusterId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(var_expirationModel) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(var_keyManager) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(var_customerMasterKeySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(var_keySpec) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(var_encryptionAlgorithms) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(var_signingAlgorithms) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(var_multiRegion) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(var_multiRegionConfiguration) , ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(var_pendingDeletionWindowInDays) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType (Dafny.ISequence<byte> value) {
 return new System.IO.MemoryStream(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType (System.IO.MemoryStream value) {
 return Dafny.Sequence<byte>.FromArray(value.ToArray());
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType (Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>> value) {
 return value.ItemEnumerable.ToDictionary(pair => FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(pair.Car), pair => FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(pair.Cdr));
}
 internal static Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType (System.Collections.Generic.Dictionary<string, string> value) {
 return Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromCollection(value.Select(pair =>
    new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(pair.Key), ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(pair.Value))
));
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType (Dafny.ISequence<byte> value) {
 return new System.IO.MemoryStream(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType (System.IO.MemoryStream value) {
 return Dafny.Sequence<byte>.FromArray(value.ToArray());
}
 internal static int FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType (int value) {
 return value;
}
 internal static int ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType (int value) {
 return value;
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry> value) {
 return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member).ToArray());
}
 internal static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType (Dafny.ISequence<byte> value) {
 return new System.IO.MemoryStream(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType (System.IO.MemoryStream value) {
 return Dafny.Sequence<byte>.FromArray(value.ToArray());
}
 internal static int FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType (int value) {
 return value;
}
 internal static int ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType (int value) {
 return value;
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static System.DateTime FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType (Dafny.ISequence<char> value) {
 System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
string timestampString = new string(value.Elements);
return System.DateTime.ParseExact(timestampString, "s", culture);

}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType (System.DateTime value) {
 System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
string timestampString = value.ToString("s", culture);
return Dafny.Sequence<char>.FromString(timestampString);

}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member).Select<Amazon.KeyManagementService.EncryptionAlgorithmSpec, string>(x => x));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.FromArray(value.Select<string, Amazon.KeyManagementService.EncryptionAlgorithmSpec>(x => x).Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member).ToArray());
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member).Select<Amazon.KeyManagementService.SigningAlgorithmSpec, string>(x => x));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.FromArray(value.Select<string, Amazon.KeyManagementService.SigningAlgorithmSpec>(x => x).Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member).ToArray());
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry> value) {
 return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry> ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member).ToArray());
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry> value) {
 return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry> ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member).ToArray());
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member));
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member).ToArray());
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static int FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType (int value) {
 return value;
}
 internal static int ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType (int value) {
 return value;
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member));
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member).ToArray());
}
 internal static Amazon.KeyManagementService.GrantOperation FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member (Amazon.KeyManagementService.GrantOperation value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(value);
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value);
}
 internal static Amazon.KeyManagementService.Model.Tag FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._ITag value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ITag ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member (Amazon.KeyManagementService.Model.Tag value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
}
 internal static Amazon.KeyManagementService.KeyUsageType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyUsageType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage (Amazon.KeyManagementService.KeyUsageType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType((Amazon.KeyManagementService.KeyUsageType) value));
}
 internal static Amazon.KeyManagementService.KeyState FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyState) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState (Amazon.KeyManagementService.KeyState value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState((Amazon.KeyManagementService.KeyState) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static Amazon.KeyManagementService.OriginType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> value) {
 return value.is_None ? (Amazon.KeyManagementService.OriginType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin (Amazon.KeyManagementService.OriginType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType((Amazon.KeyManagementService.OriginType) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
}
 internal static Amazon.KeyManagementService.ExpirationModelType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> value) {
 return value.is_None ? (Amazon.KeyManagementService.ExpirationModelType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel (Amazon.KeyManagementService.ExpirationModelType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType((Amazon.KeyManagementService.ExpirationModelType) value));
}
 internal static Amazon.KeyManagementService.KeyManagerType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeyManagerType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager (Amazon.KeyManagementService.KeyManagerType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType((Amazon.KeyManagementService.KeyManagerType) value));
}
 internal static Amazon.KeyManagementService.CustomerMasterKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec (Amazon.KeyManagementService.CustomerMasterKeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec((Amazon.KeyManagementService.CustomerMasterKeySpec) value));
}
 internal static Amazon.KeyManagementService.KeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> value) {
 return value.is_None ? (Amazon.KeyManagementService.KeySpec) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec (Amazon.KeyManagementService.KeySpec value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList((System.Collections.Generic.List<string>) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList((System.Collections.Generic.List<string>) value));
}
 internal static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion (Wrappers_Compile._IOption<bool> value) {
 return value.is_None ? (bool?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(value.Extract());
}
 internal static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion (bool? value) {
 return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType((bool) value));
}
 internal static Amazon.KeyManagementService.Model.MultiRegionConfiguration FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.MultiRegionConfiguration) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration (Amazon.KeyManagementService.Model.MultiRegionConfiguration value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration((Amazon.KeyManagementService.Model.MultiRegionConfiguration) value));
}
 internal static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(value);
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoresListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member (Amazon.KeyManagementService.Model.CustomKeyStoresListEntry value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(value);
}
 internal static Amazon.KeyManagementService.EncryptionAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member (Amazon.KeyManagementService.EncryptionAlgorithmSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value);
}
 internal static Amazon.KeyManagementService.SigningAlgorithmSpec FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member (Amazon.KeyManagementService.SigningAlgorithmSpec value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
}
 internal static Amazon.KeyManagementService.Model.AliasListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member (Amazon.KeyManagementService.Model.AliasListEntry value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(value);
}
 internal static Amazon.KeyManagementService.Model.GrantListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member (Amazon.KeyManagementService.Model.GrantListEntry value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
}
 internal static Amazon.KeyManagementService.Model.Tag FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag (software.amazon.cryptography.services.kms.internaldafny.types._ITag value) {
 software.amazon.cryptography.services.kms.internaldafny.types.Tag concrete = (software.amazon.cryptography.services.kms.internaldafny.types.Tag)value; Amazon.KeyManagementService.Model.Tag converted = new Amazon.KeyManagementService.Model.Tag();  converted.TagKey = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(concrete._TagKey);
  converted.TagValue = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(concrete._TagValue); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ITag ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag (Amazon.KeyManagementService.Model.Tag value) {

 return new software.amazon.cryptography.services.kms.internaldafny.types.Tag ( ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(value.TagKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(value.TagValue) ) ;
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static Amazon.KeyManagementService.Model.MultiRegionConfiguration FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration (software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration value) {
 software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration concrete = (software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration)value; Amazon.KeyManagementService.Model.MultiRegionConfiguration converted = new Amazon.KeyManagementService.Model.MultiRegionConfiguration(); if (concrete._MultiRegionKeyType.is_Some) converted.MultiRegionKeyType = (Amazon.KeyManagementService.MultiRegionKeyType) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(concrete._MultiRegionKeyType);
 if (concrete._PrimaryKey.is_Some) converted.PrimaryKey = (Amazon.KeyManagementService.Model.MultiRegionKey) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(concrete._PrimaryKey);
 if (concrete._ReplicaKeys.is_Some) converted.ReplicaKeys = (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(concrete._ReplicaKeys); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration (Amazon.KeyManagementService.Model.MultiRegionConfiguration value) {
 Amazon.KeyManagementService.MultiRegionKeyType var_multiRegionKeyType = value.MultiRegionKeyType;
 Amazon.KeyManagementService.Model.MultiRegionKey var_primaryKey = value.PrimaryKey;
 System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> var_replicaKeys = value.ReplicaKeys;
 return new software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(var_multiRegionKeyType) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(var_primaryKey) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(var_replicaKeys) ) ;
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static Amazon.KeyManagementService.Model.CustomKeyStoresListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry (software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry value) {
 software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry concrete = (software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry)value; Amazon.KeyManagementService.Model.CustomKeyStoresListEntry converted = new Amazon.KeyManagementService.Model.CustomKeyStoresListEntry(); if (concrete._CustomKeyStoreId.is_Some) converted.CustomKeyStoreId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(concrete._CustomKeyStoreId);
 if (concrete._CustomKeyStoreName.is_Some) converted.CustomKeyStoreName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(concrete._CustomKeyStoreName);
 if (concrete._CloudHsmClusterId.is_Some) converted.CloudHsmClusterId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(concrete._CloudHsmClusterId);
 if (concrete._TrustAnchorCertificate.is_Some) converted.TrustAnchorCertificate = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(concrete._TrustAnchorCertificate);
 if (concrete._ConnectionState.is_Some) converted.ConnectionState = (Amazon.KeyManagementService.ConnectionStateType) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(concrete._ConnectionState);
 if (concrete._ConnectionErrorCode.is_Some) converted.ConnectionErrorCode = (Amazon.KeyManagementService.ConnectionErrorCodeType) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(concrete._ConnectionErrorCode);
 if (concrete._CreationDate.is_Some) converted.CreationDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(concrete._CreationDate); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry (Amazon.KeyManagementService.Model.CustomKeyStoresListEntry value) {
 string var_customKeyStoreId = value.CustomKeyStoreId;
 string var_customKeyStoreName = value.CustomKeyStoreName;
 string var_cloudHsmClusterId = value.CloudHsmClusterId;
 string var_trustAnchorCertificate = value.TrustAnchorCertificate;
 Amazon.KeyManagementService.ConnectionStateType var_connectionState = value.ConnectionState;
 Amazon.KeyManagementService.ConnectionErrorCodeType var_connectionErrorCode = value.ConnectionErrorCode;
 System.DateTime? var_creationDate = value.CreationDate;
 return new software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry ( ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(var_customKeyStoreId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(var_customKeyStoreName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(var_cloudHsmClusterId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(var_trustAnchorCertificate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(var_connectionState) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(var_connectionErrorCode) , ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(var_creationDate) ) ;
}
 internal static Amazon.KeyManagementService.Model.AliasListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry (software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry value) {
 software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry concrete = (software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry)value; Amazon.KeyManagementService.Model.AliasListEntry converted = new Amazon.KeyManagementService.Model.AliasListEntry(); if (concrete._AliasName.is_Some) converted.AliasName = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(concrete._AliasName);
 if (concrete._AliasArn.is_Some) converted.AliasArn = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(concrete._AliasArn);
 if (concrete._TargetKeyId.is_Some) converted.TargetKeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(concrete._TargetKeyId);
 if (concrete._CreationDate.is_Some) converted.CreationDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(concrete._CreationDate);
 if (concrete._LastUpdatedDate.is_Some) converted.LastUpdatedDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(concrete._LastUpdatedDate); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry (Amazon.KeyManagementService.Model.AliasListEntry value) {
 string var_aliasName = value.AliasName;
 string var_aliasArn = value.AliasArn;
 string var_targetKeyId = value.TargetKeyId;
 System.DateTime? var_creationDate = value.CreationDate;
 System.DateTime? var_lastUpdatedDate = value.LastUpdatedDate;
 return new software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(var_aliasName) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(var_aliasArn) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(var_targetKeyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(var_creationDate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(var_lastUpdatedDate) ) ;
}
 internal static Amazon.KeyManagementService.Model.GrantListEntry FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry (software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry value) {
 software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry concrete = (software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry)value; Amazon.KeyManagementService.Model.GrantListEntry converted = new Amazon.KeyManagementService.Model.GrantListEntry(); if (concrete._KeyId.is_Some) converted.KeyId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(concrete._KeyId);
 if (concrete._GrantId.is_Some) converted.GrantId = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(concrete._GrantId);
 if (concrete._Name.is_Some) converted.Name = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(concrete._Name);
 if (concrete._CreationDate.is_Some) converted.CreationDate = (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(concrete._CreationDate);
 if (concrete._GranteePrincipal.is_Some) converted.GranteePrincipal = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(concrete._GranteePrincipal);
 if (concrete._RetiringPrincipal.is_Some) converted.RetiringPrincipal = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(concrete._RetiringPrincipal);
 if (concrete._IssuingAccount.is_Some) converted.IssuingAccount = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(concrete._IssuingAccount);
 if (concrete._Operations.is_Some) converted.Operations = (System.Collections.Generic.List<string>) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(concrete._Operations);
 if (concrete._Constraints.is_Some) converted.Constraints = (Amazon.KeyManagementService.Model.GrantConstraints) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(concrete._Constraints); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry (Amazon.KeyManagementService.Model.GrantListEntry value) {
 string var_keyId = value.KeyId;
 string var_grantId = value.GrantId;
 string var_name = value.Name;
 System.DateTime? var_creationDate = value.CreationDate;
 string var_granteePrincipal = value.GranteePrincipal;
 string var_retiringPrincipal = value.RetiringPrincipal;
 string var_issuingAccount = value.IssuingAccount;
 System.Collections.Generic.List<string> var_operations = value.Operations;
 Amazon.KeyManagementService.Model.GrantConstraints var_constraints = value.Constraints;
 return new software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(var_keyId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(var_grantId) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(var_name) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(var_creationDate) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(var_granteePrincipal) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(var_retiringPrincipal) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(var_issuingAccount) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(var_operations) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(var_constraints) ) ;
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue (Dafny.ISequence<char> value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue (string value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(value);
}
 internal static Amazon.KeyManagementService.MultiRegionKeyType FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> value) {
 return value.is_None ? (Amazon.KeyManagementService.MultiRegionKeyType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType (Amazon.KeyManagementService.MultiRegionKeyType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType((Amazon.KeyManagementService.MultiRegionKeyType) value));
}
 internal static Amazon.KeyManagementService.Model.MultiRegionKey FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.MultiRegionKey) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey (Amazon.KeyManagementService.Model.MultiRegionKey value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey((Amazon.KeyManagementService.Model.MultiRegionKey) value));
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> value) {
 return value.is_None ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList((System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType((string) value));
}
 internal static Amazon.KeyManagementService.ConnectionStateType FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> value) {
 return value.is_None ? (Amazon.KeyManagementService.ConnectionStateType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState (Amazon.KeyManagementService.ConnectionStateType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType((Amazon.KeyManagementService.ConnectionStateType) value));
}
 internal static Amazon.KeyManagementService.ConnectionErrorCodeType FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> value) {
 return value.is_None ? (Amazon.KeyManagementService.ConnectionErrorCodeType) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode (Amazon.KeyManagementService.ConnectionErrorCodeType value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType((Amazon.KeyManagementService.ConnectionErrorCodeType) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType((string) value));
}
 internal static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (System.DateTime?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate (System.DateTime? value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations (Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList((System.Collections.Generic.List<string>) value));
}
 internal static Amazon.KeyManagementService.Model.GrantConstraints FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints (Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> value) {
 return value.is_None ? (Amazon.KeyManagementService.Model.GrantConstraints) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(value.Extract());
}
 internal static Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints (Amazon.KeyManagementService.Model.GrantConstraints value) {
 return value == null ? Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.create_None() : Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints((Amazon.KeyManagementService.Model.GrantConstraints) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static Amazon.KeyManagementService.Model.MultiRegionKey FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey (software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey value) {
 software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey concrete = (software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey)value; Amazon.KeyManagementService.Model.MultiRegionKey converted = new Amazon.KeyManagementService.Model.MultiRegionKey(); if (concrete._Arn.is_Some) converted.Arn = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(concrete._Arn);
 if (concrete._Region.is_Some) converted.Region = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(concrete._Region); return converted;
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey (Amazon.KeyManagementService.Model.MultiRegionKey value) {
 string var_arn = value.Arn;
 string var_region = value.Region;
 return new software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey ( ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(var_arn) , ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(var_region) ) ;
}
 internal static System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList (Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> value) {
 return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>(value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member));
}
 internal static Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> value) {
 return Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>.FromArray(value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member).ToArray());
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
}
 internal static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType((string) value));
}
 internal static Amazon.KeyManagementService.Model.MultiRegionKey FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member (software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey value) {
 return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value);
}
 internal static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member (Amazon.KeyManagementService.Model.MultiRegionKey value) {
 return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value);
}
 internal static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 public static System.Exception FromDafny_CommonError(software.amazon.cryptography.services.kms.internaldafny.types._IError value) {
 switch(value)
 {
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException dafnyVal:
return FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(dafnyVal);
 case software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque dafnyVal:
 return new SystemException(dafnyVal._obj.ToString());
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new SystemException();;
}
}
 public static software.amazon.cryptography.services.kms.internaldafny.types._IError ToDafny_CommonError(System.Exception value) {
 switch (value) {
 case Amazon.KeyManagementService.Model.AlreadyExistsException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(e);

 case Amazon.KeyManagementService.Model.CloudHsmClusterInUseException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(e);

 case Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(e);

 case Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(e);

 case Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(e);

 case Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(e);

 case Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(e);

 case Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(e);

 case Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(e);

 case Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(e);

 case Amazon.KeyManagementService.Model.DependencyTimeoutException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(e);

 case Amazon.KeyManagementService.Model.DisabledException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(e);

 case Amazon.KeyManagementService.Model.ExpiredImportTokenException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(e);

 case Amazon.KeyManagementService.Model.IncorrectKeyException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(e);

 case Amazon.KeyManagementService.Model.IncorrectKeyMaterialException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(e);

 case Amazon.KeyManagementService.Model.IncorrectTrustAnchorException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(e);

 case Amazon.KeyManagementService.Model.InvalidAliasNameException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(e);

 case Amazon.KeyManagementService.Model.InvalidArnException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(e);

 case Amazon.KeyManagementService.Model.InvalidCiphertextException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(e);

 case Amazon.KeyManagementService.Model.InvalidGrantIdException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(e);

 case Amazon.KeyManagementService.Model.InvalidGrantTokenException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(e);

 case Amazon.KeyManagementService.Model.InvalidImportTokenException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(e);

 case Amazon.KeyManagementService.Model.InvalidKeyUsageException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(e);

 case Amazon.KeyManagementService.Model.InvalidMarkerException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(e);

 case Amazon.KeyManagementService.Model.KeyUnavailableException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(e);

 case Amazon.KeyManagementService.Model.KMSInternalException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(e);

 case Amazon.KeyManagementService.Model.KMSInvalidSignatureException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(e);

 case Amazon.KeyManagementService.Model.KMSInvalidStateException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(e);

 case Amazon.KeyManagementService.Model.LimitExceededException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(e);

 case Amazon.KeyManagementService.Model.MalformedPolicyDocumentException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(e);

 case Amazon.KeyManagementService.Model.NotFoundException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(e);

 case Amazon.KeyManagementService.Model.TagException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(e);

 case Amazon.KeyManagementService.Model.UnsupportedOperationException e:
    return TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(e);

 default:
    return new software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque(value);

}
}
}
}
