// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-24T06:03:27.038099
include "../StandardLibrary/StandardLibrary.dfy"
include "../Util/UTF8.dfy"
 module {:extern "Dafny.Com.Amazonaws.Kms.KeyManagementService"} Com.Amazonaws.Kms.KeyManagementService {
 import opened Wrappers
import opened StandardLibrary.UInt
import opened UTF8
 datatype AlgorithmSpec =
	| RSAES_PKCS1_V1_5
	| RSAES_OAEP_SHA_1
	| RSAES_OAEP_SHA_256
 type AliasList = seq<AliasListEntry>
 datatype AliasListEntry = AliasListEntry (
	nameonly AliasName: Option<AliasNameType> ,
	nameonly AliasArn: Option<ArnType> ,
	nameonly TargetKeyId: Option<KeyIdType> ,
	nameonly CreationDate: Option<string> ,
	nameonly LastUpdatedDate: Option<string> )
 type AliasNameType = x: string |  ( 1 <= |x| <= 256 ) witness *
 datatype AlreadyExistsException = AlreadyExistsException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "AlreadyExistsException: " + message.value else "AlreadyExistsException"
	}
 }
 type ArnType = x: string |  ( 20 <= |x| <= 2048 ) witness *
 type AWSAccountIdType = string
 type BooleanType = bool
 datatype CancelKeyDeletionRequest = CancelKeyDeletionRequest (
	nameonly KeyId: KeyIdType )
 datatype CancelKeyDeletionResponse = CancelKeyDeletionResponse (
	nameonly KeyId: Option<KeyIdType> )
 type CiphertextType = x: seq<uint8> |  ( 1 <= |x| <= 6144 ) witness *
 type CloudHsmClusterIdType = x: string |  ( 19 <= |x| <= 24 ) witness *
 datatype CloudHsmClusterInUseException = CloudHsmClusterInUseException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CloudHsmClusterInUseException: " + message.value else "CloudHsmClusterInUseException"
	}
 }
 datatype CloudHsmClusterInvalidConfigurationException = CloudHsmClusterInvalidConfigurationException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CloudHsmClusterInvalidConfigurationException: " + message.value else "CloudHsmClusterInvalidConfigurationException"
	}
 }
 datatype CloudHsmClusterNotActiveException = CloudHsmClusterNotActiveException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CloudHsmClusterNotActiveException: " + message.value else "CloudHsmClusterNotActiveException"
	}
 }
 datatype CloudHsmClusterNotFoundException = CloudHsmClusterNotFoundException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CloudHsmClusterNotFoundException: " + message.value else "CloudHsmClusterNotFoundException"
	}
 }
 datatype CloudHsmClusterNotRelatedException = CloudHsmClusterNotRelatedException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CloudHsmClusterNotRelatedException: " + message.value else "CloudHsmClusterNotRelatedException"
	}
 }
 datatype ConnectCustomKeyStoreRequest = ConnectCustomKeyStoreRequest (
	nameonly CustomKeyStoreId: CustomKeyStoreIdType )
 datatype ConnectCustomKeyStoreResponse = ConnectCustomKeyStoreResponse (  )
 datatype ConnectionErrorCodeType =
	| INVALID_CREDENTIALS
	| CLUSTER_NOT_FOUND
	| NETWORK_ERRORS
	| INTERNAL_ERROR
	| INSUFFICIENT_CLOUDHSM_HSMS
	| USER_LOCKED_OUT
	| USER_NOT_FOUND
	| USER_LOGGED_IN
	| SUBNET_NOT_FOUND
 datatype ConnectionStateType =
	| CONNECTED
	| CONNECTING
	| FAILED
	| DISCONNECTED
	| DISCONNECTING
 datatype CreateAliasRequest = CreateAliasRequest (
	nameonly AliasName: AliasNameType ,
	nameonly TargetKeyId: KeyIdType )
 datatype CreateCustomKeyStoreRequest = CreateCustomKeyStoreRequest (
	nameonly CustomKeyStoreName: CustomKeyStoreNameType ,
	nameonly CloudHsmClusterId: CloudHsmClusterIdType ,
	nameonly TrustAnchorCertificate: TrustAnchorCertificateType ,
	nameonly KeyStorePassword: KeyStorePasswordType )
 datatype CreateCustomKeyStoreResponse = CreateCustomKeyStoreResponse (
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> )
 datatype CreateGrantRequest = CreateGrantRequest (
	nameonly KeyId: KeyIdType ,
	nameonly GranteePrincipal: PrincipalIdType ,
	nameonly RetiringPrincipal: Option<PrincipalIdType> ,
	nameonly Operations: GrantOperationList ,
	nameonly Constraints: Option<GrantConstraints> ,
	nameonly GrantTokens: Option<GrantTokenList> ,
	nameonly Name: Option<GrantNameType> )
 datatype CreateGrantResponse = CreateGrantResponse (
	nameonly GrantToken: Option<GrantTokenType> ,
	nameonly GrantId: Option<GrantIdType> )
 datatype CreateKeyRequest = CreateKeyRequest (
	nameonly Policy: Option<PolicyType> ,
	nameonly Description: Option<DescriptionType> ,
	nameonly KeyUsage: Option<KeyUsageType> ,
	nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
	nameonly KeySpec: Option<KeySpec> ,
	nameonly Origin: Option<OriginType> ,
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
	nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> ,
	nameonly Tags: Option<TagList> ,
	nameonly MultiRegion: Option<NullableBooleanType> )
 datatype CreateKeyResponse = CreateKeyResponse (
	nameonly KeyMetadata: Option<KeyMetadata> )
 datatype CustomerMasterKeySpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
	| SYMMETRIC_DEFAULT
 datatype CustomKeyStoreHasCMKsException = CustomKeyStoreHasCMKsException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CustomKeyStoreHasCMKsException: " + message.value else "CustomKeyStoreHasCMKsException"
	}
 }
 type CustomKeyStoreIdType = x: string |  ( 1 <= |x| <= 64 ) witness *
 datatype CustomKeyStoreInvalidStateException = CustomKeyStoreInvalidStateException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CustomKeyStoreInvalidStateException: " + message.value else "CustomKeyStoreInvalidStateException"
	}
 }
 datatype CustomKeyStoreNameInUseException = CustomKeyStoreNameInUseException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CustomKeyStoreNameInUseException: " + message.value else "CustomKeyStoreNameInUseException"
	}
 }
 type CustomKeyStoreNameType = x: string |  ( 1 <= |x| <= 256 ) witness *
 datatype CustomKeyStoreNotFoundException = CustomKeyStoreNotFoundException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "CustomKeyStoreNotFoundException: " + message.value else "CustomKeyStoreNotFoundException"
	}
 }
 type CustomKeyStoresList = seq<CustomKeyStoresListEntry>
 datatype CustomKeyStoresListEntry = CustomKeyStoresListEntry (
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
	nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> ,
	nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> ,
	nameonly TrustAnchorCertificate: Option<TrustAnchorCertificateType> ,
	nameonly ConnectionState: Option<ConnectionStateType> ,
	nameonly ConnectionErrorCode: Option<ConnectionErrorCodeType> ,
	nameonly CreationDate: Option<string> )
 datatype DataKeyPairSpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
 datatype DataKeySpec =
	| AES_256
	| AES_128
 datatype DecryptRequest = DecryptRequest (
	nameonly CiphertextBlob: CiphertextType ,
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly GrantTokens: Option<GrantTokenList> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> )
 datatype DecryptResponse = DecryptResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly Plaintext: Option<PlaintextType> ,
	nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> )
 datatype DeleteAliasRequest = DeleteAliasRequest (
	nameonly AliasName: AliasNameType )
 datatype DeleteCustomKeyStoreRequest = DeleteCustomKeyStoreRequest (
	nameonly CustomKeyStoreId: CustomKeyStoreIdType )
 datatype DeleteCustomKeyStoreResponse = DeleteCustomKeyStoreResponse (  )
 datatype DeleteImportedKeyMaterialRequest = DeleteImportedKeyMaterialRequest (
	nameonly KeyId: KeyIdType )
 datatype DependencyTimeoutException = DependencyTimeoutException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "DependencyTimeoutException: " + message.value else "DependencyTimeoutException"
	}
 }
 datatype DescribeCustomKeyStoresRequest = DescribeCustomKeyStoresRequest (
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
	nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> ,
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> )
 datatype DescribeCustomKeyStoresResponse = DescribeCustomKeyStoresResponse (
	nameonly CustomKeyStores: Option<CustomKeyStoresList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
 datatype DescribeKeyRequest = DescribeKeyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype DescribeKeyResponse = DescribeKeyResponse (
	nameonly KeyMetadata: Option<KeyMetadata> )
 type DescriptionType = x: string |  ( 0 <= |x| <= 8192 ) witness *
 datatype DisabledException = DisabledException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "DisabledException: " + message.value else "DisabledException"
	}
 }
 datatype DisableKeyRequest = DisableKeyRequest (
	nameonly KeyId: KeyIdType )
 datatype DisableKeyRotationRequest = DisableKeyRotationRequest (
	nameonly KeyId: KeyIdType )
 datatype DisconnectCustomKeyStoreRequest = DisconnectCustomKeyStoreRequest (
	nameonly CustomKeyStoreId: CustomKeyStoreIdType )
 datatype DisconnectCustomKeyStoreResponse = DisconnectCustomKeyStoreResponse (  )
 datatype EnableKeyRequest = EnableKeyRequest (
	nameonly KeyId: KeyIdType )
 datatype EnableKeyRotationRequest = EnableKeyRotationRequest (
	nameonly KeyId: KeyIdType )
 datatype EncryptionAlgorithmSpec =
	| SYMMETRIC_DEFAULT
	| RSAES_OAEP_SHA_1
	| RSAES_OAEP_SHA_256
 type EncryptionAlgorithmSpecList = seq<EncryptionAlgorithmSpec>
 type EncryptionContextKey = ValidUTF8Bytes
 type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>
 type EncryptionContextValue = ValidUTF8Bytes
 datatype EncryptRequest = EncryptRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Plaintext: PlaintextType ,
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly GrantTokens: Option<GrantTokenList> ,
	nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> )
 datatype EncryptResponse = EncryptResponse (
	nameonly CiphertextBlob: Option<CiphertextType> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> )
 type ErrorMessageType = string
 datatype ExpirationModelType =
	| KEY_MATERIAL_EXPIRES
	| KEY_MATERIAL_DOES_NOT_EXPIRE
 datatype ExpiredImportTokenException = ExpiredImportTokenException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "ExpiredImportTokenException: " + message.value else "ExpiredImportTokenException"
	}
 }
 datatype GenerateDataKeyPairRequest = GenerateDataKeyPairRequest (
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly KeyId: KeyIdType ,
	nameonly KeyPairSpec: DataKeyPairSpec ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype GenerateDataKeyPairResponse = GenerateDataKeyPairResponse (
	nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> ,
	nameonly PrivateKeyPlaintext: Option<PlaintextType> ,
	nameonly PublicKey: Option<PublicKeyType> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly KeyPairSpec: Option<DataKeyPairSpec> )
 datatype GenerateDataKeyPairWithoutPlaintextRequest = GenerateDataKeyPairWithoutPlaintextRequest (
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly KeyId: KeyIdType ,
	nameonly KeyPairSpec: DataKeyPairSpec ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype GenerateDataKeyPairWithoutPlaintextResponse = GenerateDataKeyPairWithoutPlaintextResponse (
	nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> ,
	nameonly PublicKey: Option<PublicKeyType> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly KeyPairSpec: Option<DataKeyPairSpec> )
 datatype GenerateDataKeyRequest = GenerateDataKeyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly NumberOfBytes: Option<NumberOfBytesType> ,
	nameonly KeySpec: Option<DataKeySpec> ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype GenerateDataKeyResponse = GenerateDataKeyResponse (
	nameonly CiphertextBlob: Option<CiphertextType> ,
	nameonly Plaintext: Option<PlaintextType> ,
	nameonly KeyId: Option<KeyIdType> )
 datatype GenerateDataKeyWithoutPlaintextRequest = GenerateDataKeyWithoutPlaintextRequest (
	nameonly KeyId: KeyIdType ,
	nameonly EncryptionContext: Option<EncryptionContextType> ,
	nameonly KeySpec: Option<DataKeySpec> ,
	nameonly NumberOfBytes: Option<NumberOfBytesType> ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype GenerateDataKeyWithoutPlaintextResponse = GenerateDataKeyWithoutPlaintextResponse (
	nameonly CiphertextBlob: Option<CiphertextType> ,
	nameonly KeyId: Option<KeyIdType> )
 datatype GenerateRandomRequest = GenerateRandomRequest (
	nameonly NumberOfBytes: Option<NumberOfBytesType> ,
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> )
 datatype GenerateRandomResponse = GenerateRandomResponse (
	nameonly Plaintext: Option<PlaintextType> )
 datatype GetKeyPolicyRequest = GetKeyPolicyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly PolicyName: PolicyNameType )
 datatype GetKeyPolicyResponse = GetKeyPolicyResponse (
	nameonly Policy: Option<PolicyType> )
 datatype GetKeyRotationStatusRequest = GetKeyRotationStatusRequest (
	nameonly KeyId: KeyIdType )
 datatype GetKeyRotationStatusResponse = GetKeyRotationStatusResponse (
	nameonly KeyRotationEnabled: Option<BooleanType> )
 datatype GetParametersForImportRequest = GetParametersForImportRequest (
	nameonly KeyId: KeyIdType ,
	nameonly WrappingAlgorithm: AlgorithmSpec ,
	nameonly WrappingKeySpec: WrappingKeySpec )
 datatype GetParametersForImportResponse = GetParametersForImportResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly ImportToken: Option<CiphertextType> ,
	nameonly PublicKey: Option<PlaintextType> ,
	nameonly ParametersValidTo: Option<string> )
 datatype GetPublicKeyRequest = GetPublicKeyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype GetPublicKeyResponse = GetPublicKeyResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly PublicKey: Option<PublicKeyType> ,
	nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
	nameonly KeySpec: Option<KeySpec> ,
	nameonly KeyUsage: Option<KeyUsageType> ,
	nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> ,
	nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> )
 datatype GrantConstraints = GrantConstraints (
	nameonly EncryptionContextSubset: Option<EncryptionContextType> ,
	nameonly EncryptionContextEquals: Option<EncryptionContextType> )
 type GrantIdType = x: string |  ( 1 <= |x| <= 128 ) witness *
 type GrantList = seq<GrantListEntry>
 datatype GrantListEntry = GrantListEntry (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly GrantId: Option<GrantIdType> ,
	nameonly Name: Option<GrantNameType> ,
	nameonly CreationDate: Option<string> ,
	nameonly GranteePrincipal: Option<PrincipalIdType> ,
	nameonly RetiringPrincipal: Option<PrincipalIdType> ,
	nameonly IssuingAccount: Option<PrincipalIdType> ,
	nameonly Operations: Option<GrantOperationList> ,
	nameonly Constraints: Option<GrantConstraints> )
 type GrantNameType = x: string |  ( 1 <= |x| <= 256 ) witness *
 datatype GrantOperation =
	| Decrypt
	| Encrypt
	| GenerateDataKey
	| GenerateDataKeyWithoutPlaintext
	| ReEncryptFrom
	| ReEncryptTo
	| Sign
	| Verify
	| GetPublicKey
	| CreateGrant
	| RetireGrant
	| DescribeKey
	| GenerateDataKeyPair
	| GenerateDataKeyPairWithoutPlaintext
 type GrantOperationList = seq<GrantOperation>
 type GrantTokenList = x: seq<GrantTokenType> |  ( 0 <= |x| <= 10 ) witness *
 type GrantTokenType = x: string |  ( 1 <= |x| <= 8192 ) witness *
 datatype ImportKeyMaterialRequest = ImportKeyMaterialRequest (
	nameonly KeyId: KeyIdType ,
	nameonly ImportToken: CiphertextType ,
	nameonly EncryptedKeyMaterial: CiphertextType ,
	nameonly ValidTo: Option<string> ,
	nameonly ExpirationModel: Option<ExpirationModelType> )
 datatype ImportKeyMaterialResponse = ImportKeyMaterialResponse (  )
 datatype IncorrectKeyException = IncorrectKeyException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "IncorrectKeyException: " + message.value else "IncorrectKeyException"
	}
 }
 datatype IncorrectKeyMaterialException = IncorrectKeyMaterialException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "IncorrectKeyMaterialException: " + message.value else "IncorrectKeyMaterialException"
	}
 }
 datatype IncorrectTrustAnchorException = IncorrectTrustAnchorException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "IncorrectTrustAnchorException: " + message.value else "IncorrectTrustAnchorException"
	}
 }
 datatype InvalidAliasNameException = InvalidAliasNameException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidAliasNameException: " + message.value else "InvalidAliasNameException"
	}
 }
 datatype InvalidArnException = InvalidArnException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidArnException: " + message.value else "InvalidArnException"
	}
 }
 datatype InvalidCiphertextException = InvalidCiphertextException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidCiphertextException: " + message.value else "InvalidCiphertextException"
	}
 }
 datatype InvalidGrantIdException = InvalidGrantIdException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidGrantIdException: " + message.value else "InvalidGrantIdException"
	}
 }
 datatype InvalidGrantTokenException = InvalidGrantTokenException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidGrantTokenException: " + message.value else "InvalidGrantTokenException"
	}
 }
 datatype InvalidImportTokenException = InvalidImportTokenException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidImportTokenException: " + message.value else "InvalidImportTokenException"
	}
 }
 datatype InvalidKeyUsageException = InvalidKeyUsageException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidKeyUsageException: " + message.value else "InvalidKeyUsageException"
	}
 }
 datatype InvalidMarkerException = InvalidMarkerException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "InvalidMarkerException: " + message.value else "InvalidMarkerException"
	}
 }
 type KeyIdType = x: string |  ( 1 <= |x| <= 2048 ) witness *
 type KeyList = seq<KeyListEntry>
 datatype KeyListEntry = KeyListEntry (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly KeyArn: Option<ArnType> )
 trait IKeyManagementServiceClient {
 predicate {:opaque} CancelKeyDeletionCalledWith (client: IKeyManagementServiceClient , input: CancelKeyDeletionRequest ) {true}
 predicate {:opaque} CancelKeyDeletionSucceededWith ( client: IKeyManagementServiceClient , input: CancelKeyDeletionRequest , output: CancelKeyDeletionResponse ) {true}
 method CancelKeyDeletion ( input: CancelKeyDeletionRequest ) returns  ( output: Result<CancelKeyDeletionResponse, KeyManagementServiceError> )
	ensures CancelKeyDeletionCalledWith(this , input )
	ensures output.Success? ==> CancelKeyDeletionSucceededWith(this , input , output.value )

 predicate {:opaque} ConnectCustomKeyStoreCalledWith (client: IKeyManagementServiceClient , input: ConnectCustomKeyStoreRequest ) {true}
 predicate {:opaque} ConnectCustomKeyStoreSucceededWith ( client: IKeyManagementServiceClient , input: ConnectCustomKeyStoreRequest , output: ConnectCustomKeyStoreResponse ) {true}
 method ConnectCustomKeyStore ( input: ConnectCustomKeyStoreRequest ) returns  ( output: Result<ConnectCustomKeyStoreResponse, KeyManagementServiceError> )
	ensures ConnectCustomKeyStoreCalledWith(this , input )
	ensures output.Success? ==> ConnectCustomKeyStoreSucceededWith(this , input , output.value )

 predicate {:opaque} CreateAliasCalledWith (client: IKeyManagementServiceClient , input: CreateAliasRequest ) {true}
 predicate {:opaque} CreateAliasSucceededWith ( client: IKeyManagementServiceClient , input: CreateAliasRequest ) {true}
 method CreateAlias ( input: CreateAliasRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures CreateAliasCalledWith(this , input )
	ensures output.Success? ==> CreateAliasSucceededWith(this , input )

 predicate {:opaque} CreateCustomKeyStoreCalledWith (client: IKeyManagementServiceClient , input: CreateCustomKeyStoreRequest ) {true}
 predicate {:opaque} CreateCustomKeyStoreSucceededWith ( client: IKeyManagementServiceClient , input: CreateCustomKeyStoreRequest , output: CreateCustomKeyStoreResponse ) {true}
 method CreateCustomKeyStore ( input: CreateCustomKeyStoreRequest ) returns  ( output: Result<CreateCustomKeyStoreResponse, KeyManagementServiceError> )
	ensures CreateCustomKeyStoreCalledWith(this , input )
	ensures output.Success? ==> CreateCustomKeyStoreSucceededWith(this , input , output.value )

 predicate {:opaque} CreateGrantCalledWith (client: IKeyManagementServiceClient , input: CreateGrantRequest ) {true}
 predicate {:opaque} CreateGrantSucceededWith ( client: IKeyManagementServiceClient , input: CreateGrantRequest , output: CreateGrantResponse ) {true}
 method CreateGrant ( input: CreateGrantRequest ) returns  ( output: Result<CreateGrantResponse, KeyManagementServiceError> )
	ensures CreateGrantCalledWith(this , input )
	ensures output.Success? ==> CreateGrantSucceededWith(this , input , output.value )

 predicate {:opaque} CreateKeyCalledWith (client: IKeyManagementServiceClient , input: CreateKeyRequest ) {true}
 predicate {:opaque} CreateKeySucceededWith ( client: IKeyManagementServiceClient , input: CreateKeyRequest , output: CreateKeyResponse ) {true}
 method CreateKey ( input: CreateKeyRequest ) returns  ( output: Result<CreateKeyResponse, KeyManagementServiceError> )
	ensures CreateKeyCalledWith(this , input )
	ensures output.Success? ==> CreateKeySucceededWith(this , input , output.value )

 predicate {:opaque} DecryptCalledWith (client: IKeyManagementServiceClient , input: DecryptRequest ) {true}
 predicate {:opaque} DecryptSucceededWith ( client: IKeyManagementServiceClient , input: DecryptRequest , output: DecryptResponse ) {true}
 method Decrypt ( input: DecryptRequest ) returns  ( output: Result<DecryptResponse, KeyManagementServiceError> )
	ensures DecryptCalledWith(this , input )
	ensures output.Success? ==> DecryptSucceededWith(this , input , output.value )

 predicate {:opaque} DeleteAliasCalledWith (client: IKeyManagementServiceClient , input: DeleteAliasRequest ) {true}
 predicate {:opaque} DeleteAliasSucceededWith ( client: IKeyManagementServiceClient , input: DeleteAliasRequest ) {true}
 method DeleteAlias ( input: DeleteAliasRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures DeleteAliasCalledWith(this , input )
	ensures output.Success? ==> DeleteAliasSucceededWith(this , input )

 predicate {:opaque} DeleteCustomKeyStoreCalledWith (client: IKeyManagementServiceClient , input: DeleteCustomKeyStoreRequest ) {true}
 predicate {:opaque} DeleteCustomKeyStoreSucceededWith ( client: IKeyManagementServiceClient , input: DeleteCustomKeyStoreRequest , output: DeleteCustomKeyStoreResponse ) {true}
 method DeleteCustomKeyStore ( input: DeleteCustomKeyStoreRequest ) returns  ( output: Result<DeleteCustomKeyStoreResponse, KeyManagementServiceError> )
	ensures DeleteCustomKeyStoreCalledWith(this , input )
	ensures output.Success? ==> DeleteCustomKeyStoreSucceededWith(this , input , output.value )

 predicate {:opaque} DeleteImportedKeyMaterialCalledWith (client: IKeyManagementServiceClient , input: DeleteImportedKeyMaterialRequest ) {true}
 predicate {:opaque} DeleteImportedKeyMaterialSucceededWith ( client: IKeyManagementServiceClient , input: DeleteImportedKeyMaterialRequest ) {true}
 method DeleteImportedKeyMaterial ( input: DeleteImportedKeyMaterialRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures DeleteImportedKeyMaterialCalledWith(this , input )
	ensures output.Success? ==> DeleteImportedKeyMaterialSucceededWith(this , input )

 predicate {:opaque} DescribeCustomKeyStoresCalledWith (client: IKeyManagementServiceClient , input: DescribeCustomKeyStoresRequest ) {true}
 predicate {:opaque} DescribeCustomKeyStoresSucceededWith ( client: IKeyManagementServiceClient , input: DescribeCustomKeyStoresRequest , output: DescribeCustomKeyStoresResponse ) {true}
 method DescribeCustomKeyStores ( input: DescribeCustomKeyStoresRequest ) returns  ( output: Result<DescribeCustomKeyStoresResponse, KeyManagementServiceError> )
	ensures DescribeCustomKeyStoresCalledWith(this , input )
	ensures output.Success? ==> DescribeCustomKeyStoresSucceededWith(this , input , output.value )

 predicate {:opaque} DescribeKeyCalledWith (client: IKeyManagementServiceClient , input: DescribeKeyRequest ) {true}
 predicate {:opaque} DescribeKeySucceededWith ( client: IKeyManagementServiceClient , input: DescribeKeyRequest , output: DescribeKeyResponse ) {true}
 method DescribeKey ( input: DescribeKeyRequest ) returns  ( output: Result<DescribeKeyResponse, KeyManagementServiceError> )
	ensures DescribeKeyCalledWith(this , input )
	ensures output.Success? ==> DescribeKeySucceededWith(this , input , output.value )

 predicate {:opaque} DisableKeyCalledWith (client: IKeyManagementServiceClient , input: DisableKeyRequest ) {true}
 predicate {:opaque} DisableKeySucceededWith ( client: IKeyManagementServiceClient , input: DisableKeyRequest ) {true}
 method DisableKey ( input: DisableKeyRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures DisableKeyCalledWith(this , input )
	ensures output.Success? ==> DisableKeySucceededWith(this , input )

 predicate {:opaque} DisableKeyRotationCalledWith (client: IKeyManagementServiceClient , input: DisableKeyRotationRequest ) {true}
 predicate {:opaque} DisableKeyRotationSucceededWith ( client: IKeyManagementServiceClient , input: DisableKeyRotationRequest ) {true}
 method DisableKeyRotation ( input: DisableKeyRotationRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures DisableKeyRotationCalledWith(this , input )
	ensures output.Success? ==> DisableKeyRotationSucceededWith(this , input )

 predicate {:opaque} DisconnectCustomKeyStoreCalledWith (client: IKeyManagementServiceClient , input: DisconnectCustomKeyStoreRequest ) {true}
 predicate {:opaque} DisconnectCustomKeyStoreSucceededWith ( client: IKeyManagementServiceClient , input: DisconnectCustomKeyStoreRequest , output: DisconnectCustomKeyStoreResponse ) {true}
 method DisconnectCustomKeyStore ( input: DisconnectCustomKeyStoreRequest ) returns  ( output: Result<DisconnectCustomKeyStoreResponse, KeyManagementServiceError> )
	ensures DisconnectCustomKeyStoreCalledWith(this , input )
	ensures output.Success? ==> DisconnectCustomKeyStoreSucceededWith(this , input , output.value )

 predicate {:opaque} EnableKeyCalledWith (client: IKeyManagementServiceClient , input: EnableKeyRequest ) {true}
 predicate {:opaque} EnableKeySucceededWith ( client: IKeyManagementServiceClient , input: EnableKeyRequest ) {true}
 method EnableKey ( input: EnableKeyRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures EnableKeyCalledWith(this , input )
	ensures output.Success? ==> EnableKeySucceededWith(this , input )

 predicate {:opaque} EnableKeyRotationCalledWith (client: IKeyManagementServiceClient , input: EnableKeyRotationRequest ) {true}
 predicate {:opaque} EnableKeyRotationSucceededWith ( client: IKeyManagementServiceClient , input: EnableKeyRotationRequest ) {true}
 method EnableKeyRotation ( input: EnableKeyRotationRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures EnableKeyRotationCalledWith(this , input )
	ensures output.Success? ==> EnableKeyRotationSucceededWith(this , input )

 predicate {:opaque} EncryptCalledWith (client: IKeyManagementServiceClient , input: EncryptRequest ) {true}
 predicate {:opaque} EncryptSucceededWith ( client: IKeyManagementServiceClient , input: EncryptRequest , output: EncryptResponse ) {true}
 method Encrypt ( input: EncryptRequest ) returns  ( output: Result<EncryptResponse, KeyManagementServiceError> )
	ensures EncryptCalledWith(this , input )
	ensures output.Success? ==> EncryptSucceededWith(this , input , output.value )

 predicate {:opaque} GenerateDataKeyCalledWith (client: IKeyManagementServiceClient , input: GenerateDataKeyRequest ) {true}
 predicate {:opaque} GenerateDataKeySucceededWith ( client: IKeyManagementServiceClient , input: GenerateDataKeyRequest , output: GenerateDataKeyResponse ) {true}
 method GenerateDataKey ( input: GenerateDataKeyRequest ) returns  ( output: Result<GenerateDataKeyResponse, KeyManagementServiceError> )
	ensures GenerateDataKeyCalledWith(this , input )
	ensures output.Success? ==> GenerateDataKeySucceededWith(this , input , output.value )

 predicate {:opaque} GenerateDataKeyPairCalledWith (client: IKeyManagementServiceClient , input: GenerateDataKeyPairRequest ) {true}
 predicate {:opaque} GenerateDataKeyPairSucceededWith ( client: IKeyManagementServiceClient , input: GenerateDataKeyPairRequest , output: GenerateDataKeyPairResponse ) {true}
 method GenerateDataKeyPair ( input: GenerateDataKeyPairRequest ) returns  ( output: Result<GenerateDataKeyPairResponse, KeyManagementServiceError> )
	ensures GenerateDataKeyPairCalledWith(this , input )
	ensures output.Success? ==> GenerateDataKeyPairSucceededWith(this , input , output.value )

 predicate {:opaque} GenerateDataKeyPairWithoutPlaintextCalledWith (client: IKeyManagementServiceClient , input: GenerateDataKeyPairWithoutPlaintextRequest ) {true}
 predicate {:opaque} GenerateDataKeyPairWithoutPlaintextSucceededWith ( client: IKeyManagementServiceClient , input: GenerateDataKeyPairWithoutPlaintextRequest , output: GenerateDataKeyPairWithoutPlaintextResponse ) {true}
 method GenerateDataKeyPairWithoutPlaintext ( input: GenerateDataKeyPairWithoutPlaintextRequest ) returns  ( output: Result<GenerateDataKeyPairWithoutPlaintextResponse, KeyManagementServiceError> )
	ensures GenerateDataKeyPairWithoutPlaintextCalledWith(this , input )
	ensures output.Success? ==> GenerateDataKeyPairWithoutPlaintextSucceededWith(this , input , output.value )

 predicate {:opaque} GenerateDataKeyWithoutPlaintextCalledWith (client: IKeyManagementServiceClient , input: GenerateDataKeyWithoutPlaintextRequest ) {true}
 predicate {:opaque} GenerateDataKeyWithoutPlaintextSucceededWith ( client: IKeyManagementServiceClient , input: GenerateDataKeyWithoutPlaintextRequest , output: GenerateDataKeyWithoutPlaintextResponse ) {true}
 method GenerateDataKeyWithoutPlaintext ( input: GenerateDataKeyWithoutPlaintextRequest ) returns  ( output: Result<GenerateDataKeyWithoutPlaintextResponse, KeyManagementServiceError> )
	ensures GenerateDataKeyWithoutPlaintextCalledWith(this , input )
	ensures output.Success? ==> GenerateDataKeyWithoutPlaintextSucceededWith(this , input , output.value )

 predicate {:opaque} GenerateRandomCalledWith (client: IKeyManagementServiceClient , input: GenerateRandomRequest ) {true}
 predicate {:opaque} GenerateRandomSucceededWith ( client: IKeyManagementServiceClient , input: GenerateRandomRequest , output: GenerateRandomResponse ) {true}
 method GenerateRandom ( input: GenerateRandomRequest ) returns  ( output: Result<GenerateRandomResponse, KeyManagementServiceError> )
	ensures GenerateRandomCalledWith(this , input )
	ensures output.Success? ==> GenerateRandomSucceededWith(this , input , output.value )

 predicate {:opaque} GetKeyPolicyCalledWith (client: IKeyManagementServiceClient , input: GetKeyPolicyRequest ) {true}
 predicate {:opaque} GetKeyPolicySucceededWith ( client: IKeyManagementServiceClient , input: GetKeyPolicyRequest , output: GetKeyPolicyResponse ) {true}
 method GetKeyPolicy ( input: GetKeyPolicyRequest ) returns  ( output: Result<GetKeyPolicyResponse, KeyManagementServiceError> )
	ensures GetKeyPolicyCalledWith(this , input )
	ensures output.Success? ==> GetKeyPolicySucceededWith(this , input , output.value )

 predicate {:opaque} GetKeyRotationStatusCalledWith (client: IKeyManagementServiceClient , input: GetKeyRotationStatusRequest ) {true}
 predicate {:opaque} GetKeyRotationStatusSucceededWith ( client: IKeyManagementServiceClient , input: GetKeyRotationStatusRequest , output: GetKeyRotationStatusResponse ) {true}
 method GetKeyRotationStatus ( input: GetKeyRotationStatusRequest ) returns  ( output: Result<GetKeyRotationStatusResponse, KeyManagementServiceError> )
	ensures GetKeyRotationStatusCalledWith(this , input )
	ensures output.Success? ==> GetKeyRotationStatusSucceededWith(this , input , output.value )

 predicate {:opaque} GetParametersForImportCalledWith (client: IKeyManagementServiceClient , input: GetParametersForImportRequest ) {true}
 predicate {:opaque} GetParametersForImportSucceededWith ( client: IKeyManagementServiceClient , input: GetParametersForImportRequest , output: GetParametersForImportResponse ) {true}
 method GetParametersForImport ( input: GetParametersForImportRequest ) returns  ( output: Result<GetParametersForImportResponse, KeyManagementServiceError> )
	ensures GetParametersForImportCalledWith(this , input )
	ensures output.Success? ==> GetParametersForImportSucceededWith(this , input , output.value )

 predicate {:opaque} GetPublicKeyCalledWith (client: IKeyManagementServiceClient , input: GetPublicKeyRequest ) {true}
 predicate {:opaque} GetPublicKeySucceededWith ( client: IKeyManagementServiceClient , input: GetPublicKeyRequest , output: GetPublicKeyResponse ) {true}
 method GetPublicKey ( input: GetPublicKeyRequest ) returns  ( output: Result<GetPublicKeyResponse, KeyManagementServiceError> )
	ensures GetPublicKeyCalledWith(this , input )
	ensures output.Success? ==> GetPublicKeySucceededWith(this , input , output.value )

 predicate {:opaque} ImportKeyMaterialCalledWith (client: IKeyManagementServiceClient , input: ImportKeyMaterialRequest ) {true}
 predicate {:opaque} ImportKeyMaterialSucceededWith ( client: IKeyManagementServiceClient , input: ImportKeyMaterialRequest , output: ImportKeyMaterialResponse ) {true}
 method ImportKeyMaterial ( input: ImportKeyMaterialRequest ) returns  ( output: Result<ImportKeyMaterialResponse, KeyManagementServiceError> )
	ensures ImportKeyMaterialCalledWith(this , input )
	ensures output.Success? ==> ImportKeyMaterialSucceededWith(this , input , output.value )

 predicate {:opaque} ListAliasesCalledWith (client: IKeyManagementServiceClient , input: ListAliasesRequest ) {true}
 predicate {:opaque} ListAliasesSucceededWith ( client: IKeyManagementServiceClient , input: ListAliasesRequest , output: ListAliasesResponse ) {true}
 method ListAliases ( input: ListAliasesRequest ) returns  ( output: Result<ListAliasesResponse, KeyManagementServiceError> )
	ensures ListAliasesCalledWith(this , input )
	ensures output.Success? ==> ListAliasesSucceededWith(this , input , output.value )

 predicate {:opaque} ListGrantsCalledWith (client: IKeyManagementServiceClient , input: ListGrantsRequest ) {true}
 predicate {:opaque} ListGrantsSucceededWith ( client: IKeyManagementServiceClient , input: ListGrantsRequest , output: ListGrantsResponse ) {true}
 method ListGrants ( input: ListGrantsRequest ) returns  ( output: Result<ListGrantsResponse, KeyManagementServiceError> )
	ensures ListGrantsCalledWith(this , input )
	ensures output.Success? ==> ListGrantsSucceededWith(this , input , output.value )

 predicate {:opaque} ListKeyPoliciesCalledWith (client: IKeyManagementServiceClient , input: ListKeyPoliciesRequest ) {true}
 predicate {:opaque} ListKeyPoliciesSucceededWith ( client: IKeyManagementServiceClient , input: ListKeyPoliciesRequest , output: ListKeyPoliciesResponse ) {true}
 method ListKeyPolicies ( input: ListKeyPoliciesRequest ) returns  ( output: Result<ListKeyPoliciesResponse, KeyManagementServiceError> )
	ensures ListKeyPoliciesCalledWith(this , input )
	ensures output.Success? ==> ListKeyPoliciesSucceededWith(this , input , output.value )

 predicate {:opaque} ListResourceTagsCalledWith (client: IKeyManagementServiceClient , input: ListResourceTagsRequest ) {true}
 predicate {:opaque} ListResourceTagsSucceededWith ( client: IKeyManagementServiceClient , input: ListResourceTagsRequest , output: ListResourceTagsResponse ) {true}
 method ListResourceTags ( input: ListResourceTagsRequest ) returns  ( output: Result<ListResourceTagsResponse, KeyManagementServiceError> )
	ensures ListResourceTagsCalledWith(this , input )
	ensures output.Success? ==> ListResourceTagsSucceededWith(this , input , output.value )

 predicate {:opaque} ListRetirableGrantsCalledWith (client: IKeyManagementServiceClient , input: ListRetirableGrantsRequest ) {true}
 predicate {:opaque} ListRetirableGrantsSucceededWith ( client: IKeyManagementServiceClient , input: ListRetirableGrantsRequest , output: ListGrantsResponse ) {true}
 method ListRetirableGrants ( input: ListRetirableGrantsRequest ) returns  ( output: Result<ListGrantsResponse, KeyManagementServiceError> )
	ensures ListRetirableGrantsCalledWith(this , input )
	ensures output.Success? ==> ListRetirableGrantsSucceededWith(this , input , output.value )

 predicate {:opaque} PutKeyPolicyCalledWith (client: IKeyManagementServiceClient , input: PutKeyPolicyRequest ) {true}
 predicate {:opaque} PutKeyPolicySucceededWith ( client: IKeyManagementServiceClient , input: PutKeyPolicyRequest ) {true}
 method PutKeyPolicy ( input: PutKeyPolicyRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures PutKeyPolicyCalledWith(this , input )
	ensures output.Success? ==> PutKeyPolicySucceededWith(this , input )

 predicate {:opaque} ReEncryptCalledWith (client: IKeyManagementServiceClient , input: ReEncryptRequest ) {true}
 predicate {:opaque} ReEncryptSucceededWith ( client: IKeyManagementServiceClient , input: ReEncryptRequest , output: ReEncryptResponse ) {true}
 method ReEncrypt ( input: ReEncryptRequest ) returns  ( output: Result<ReEncryptResponse, KeyManagementServiceError> )
	ensures ReEncryptCalledWith(this , input )
	ensures output.Success? ==> ReEncryptSucceededWith(this , input , output.value )

 predicate {:opaque} ReplicateKeyCalledWith (client: IKeyManagementServiceClient , input: ReplicateKeyRequest ) {true}
 predicate {:opaque} ReplicateKeySucceededWith ( client: IKeyManagementServiceClient , input: ReplicateKeyRequest , output: ReplicateKeyResponse ) {true}
 method ReplicateKey ( input: ReplicateKeyRequest ) returns  ( output: Result<ReplicateKeyResponse, KeyManagementServiceError> )
	ensures ReplicateKeyCalledWith(this , input )
	ensures output.Success? ==> ReplicateKeySucceededWith(this , input , output.value )

 predicate {:opaque} RetireGrantCalledWith (client: IKeyManagementServiceClient , input: RetireGrantRequest ) {true}
 predicate {:opaque} RetireGrantSucceededWith ( client: IKeyManagementServiceClient , input: RetireGrantRequest ) {true}
 method RetireGrant ( input: RetireGrantRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures RetireGrantCalledWith(this , input )
	ensures output.Success? ==> RetireGrantSucceededWith(this , input )

 predicate {:opaque} RevokeGrantCalledWith (client: IKeyManagementServiceClient , input: RevokeGrantRequest ) {true}
 predicate {:opaque} RevokeGrantSucceededWith ( client: IKeyManagementServiceClient , input: RevokeGrantRequest ) {true}
 method RevokeGrant ( input: RevokeGrantRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures RevokeGrantCalledWith(this , input )
	ensures output.Success? ==> RevokeGrantSucceededWith(this , input )

 predicate {:opaque} ScheduleKeyDeletionCalledWith (client: IKeyManagementServiceClient , input: ScheduleKeyDeletionRequest ) {true}
 predicate {:opaque} ScheduleKeyDeletionSucceededWith ( client: IKeyManagementServiceClient , input: ScheduleKeyDeletionRequest , output: ScheduleKeyDeletionResponse ) {true}
 method ScheduleKeyDeletion ( input: ScheduleKeyDeletionRequest ) returns  ( output: Result<ScheduleKeyDeletionResponse, KeyManagementServiceError> )
	ensures ScheduleKeyDeletionCalledWith(this , input )
	ensures output.Success? ==> ScheduleKeyDeletionSucceededWith(this , input , output.value )

 predicate {:opaque} SignCalledWith (client: IKeyManagementServiceClient , input: SignRequest ) {true}
 predicate {:opaque} SignSucceededWith ( client: IKeyManagementServiceClient , input: SignRequest , output: SignResponse ) {true}
 method Sign ( input: SignRequest ) returns  ( output: Result<SignResponse, KeyManagementServiceError> )
	ensures SignCalledWith(this , input )
	ensures output.Success? ==> SignSucceededWith(this , input , output.value )

 predicate {:opaque} TagResourceCalledWith (client: IKeyManagementServiceClient , input: TagResourceRequest ) {true}
 predicate {:opaque} TagResourceSucceededWith ( client: IKeyManagementServiceClient , input: TagResourceRequest ) {true}
 method TagResource ( input: TagResourceRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures TagResourceCalledWith(this , input )
	ensures output.Success? ==> TagResourceSucceededWith(this , input )

 predicate {:opaque} UntagResourceCalledWith (client: IKeyManagementServiceClient , input: UntagResourceRequest ) {true}
 predicate {:opaque} UntagResourceSucceededWith ( client: IKeyManagementServiceClient , input: UntagResourceRequest ) {true}
 method UntagResource ( input: UntagResourceRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures UntagResourceCalledWith(this , input )
	ensures output.Success? ==> UntagResourceSucceededWith(this , input )

 predicate {:opaque} UpdateAliasCalledWith (client: IKeyManagementServiceClient , input: UpdateAliasRequest ) {true}
 predicate {:opaque} UpdateAliasSucceededWith ( client: IKeyManagementServiceClient , input: UpdateAliasRequest ) {true}
 method UpdateAlias ( input: UpdateAliasRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures UpdateAliasCalledWith(this , input )
	ensures output.Success? ==> UpdateAliasSucceededWith(this , input )

 predicate {:opaque} UpdateCustomKeyStoreCalledWith (client: IKeyManagementServiceClient , input: UpdateCustomKeyStoreRequest ) {true}
 predicate {:opaque} UpdateCustomKeyStoreSucceededWith ( client: IKeyManagementServiceClient , input: UpdateCustomKeyStoreRequest , output: UpdateCustomKeyStoreResponse ) {true}
 method UpdateCustomKeyStore ( input: UpdateCustomKeyStoreRequest ) returns  ( output: Result<UpdateCustomKeyStoreResponse, KeyManagementServiceError> )
	ensures UpdateCustomKeyStoreCalledWith(this , input )
	ensures output.Success? ==> UpdateCustomKeyStoreSucceededWith(this , input , output.value )

 predicate {:opaque} UpdateKeyDescriptionCalledWith (client: IKeyManagementServiceClient , input: UpdateKeyDescriptionRequest ) {true}
 predicate {:opaque} UpdateKeyDescriptionSucceededWith ( client: IKeyManagementServiceClient , input: UpdateKeyDescriptionRequest ) {true}
 method UpdateKeyDescription ( input: UpdateKeyDescriptionRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures UpdateKeyDescriptionCalledWith(this , input )
	ensures output.Success? ==> UpdateKeyDescriptionSucceededWith(this , input )

 predicate {:opaque} UpdatePrimaryRegionCalledWith (client: IKeyManagementServiceClient , input: UpdatePrimaryRegionRequest ) {true}
 predicate {:opaque} UpdatePrimaryRegionSucceededWith ( client: IKeyManagementServiceClient , input: UpdatePrimaryRegionRequest ) {true}
 method UpdatePrimaryRegion ( input: UpdatePrimaryRegionRequest ) returns  ( output: Result<(), KeyManagementServiceError> )
	ensures UpdatePrimaryRegionCalledWith(this , input )
	ensures output.Success? ==> UpdatePrimaryRegionSucceededWith(this , input )

 predicate {:opaque} VerifyCalledWith (client: IKeyManagementServiceClient , input: VerifyRequest ) {true}
 predicate {:opaque} VerifySucceededWith ( client: IKeyManagementServiceClient , input: VerifyRequest , output: VerifyResponse ) {true}
 method Verify ( input: VerifyRequest ) returns  ( output: Result<VerifyResponse, KeyManagementServiceError> )
	ensures VerifyCalledWith(this , input )
	ensures output.Success? ==> VerifySucceededWith(this , input , output.value )

}
 datatype KeyManagementServiceError =
 | KeyManagementService_AlreadyExistsException(AlreadyExistsException: AlreadyExistsException)
 | KeyManagementService_CloudHsmClusterInUseException(CloudHsmClusterInUseException: CloudHsmClusterInUseException)
 | KeyManagementService_CloudHsmClusterInvalidConfigurationException(CloudHsmClusterInvalidConfigurationException: CloudHsmClusterInvalidConfigurationException)
 | KeyManagementService_CloudHsmClusterNotActiveException(CloudHsmClusterNotActiveException: CloudHsmClusterNotActiveException)
 | KeyManagementService_CloudHsmClusterNotFoundException(CloudHsmClusterNotFoundException: CloudHsmClusterNotFoundException)
 | KeyManagementService_CloudHsmClusterNotRelatedException(CloudHsmClusterNotRelatedException: CloudHsmClusterNotRelatedException)
 | KeyManagementService_CustomKeyStoreHasCMKsException(CustomKeyStoreHasCMKsException: CustomKeyStoreHasCMKsException)
 | KeyManagementService_CustomKeyStoreInvalidStateException(CustomKeyStoreInvalidStateException: CustomKeyStoreInvalidStateException)
 | KeyManagementService_CustomKeyStoreNameInUseException(CustomKeyStoreNameInUseException: CustomKeyStoreNameInUseException)
 | KeyManagementService_CustomKeyStoreNotFoundException(CustomKeyStoreNotFoundException: CustomKeyStoreNotFoundException)
 | KeyManagementService_DependencyTimeoutException(DependencyTimeoutException: DependencyTimeoutException)
 | KeyManagementService_DisabledException(DisabledException: DisabledException)
 | KeyManagementService_ExpiredImportTokenException(ExpiredImportTokenException: ExpiredImportTokenException)
 | KeyManagementService_IncorrectKeyException(IncorrectKeyException: IncorrectKeyException)
 | KeyManagementService_IncorrectKeyMaterialException(IncorrectKeyMaterialException: IncorrectKeyMaterialException)
 | KeyManagementService_IncorrectTrustAnchorException(IncorrectTrustAnchorException: IncorrectTrustAnchorException)
 | KeyManagementService_InvalidAliasNameException(InvalidAliasNameException: InvalidAliasNameException)
 | KeyManagementService_InvalidArnException(InvalidArnException: InvalidArnException)
 | KeyManagementService_InvalidCiphertextException(InvalidCiphertextException: InvalidCiphertextException)
 | KeyManagementService_InvalidGrantIdException(InvalidGrantIdException: InvalidGrantIdException)
 | KeyManagementService_InvalidGrantTokenException(InvalidGrantTokenException: InvalidGrantTokenException)
 | KeyManagementService_InvalidImportTokenException(InvalidImportTokenException: InvalidImportTokenException)
 | KeyManagementService_InvalidKeyUsageException(InvalidKeyUsageException: InvalidKeyUsageException)
 | KeyManagementService_InvalidMarkerException(InvalidMarkerException: InvalidMarkerException)
 | KeyManagementService_KeyUnavailableException(KeyUnavailableException: KeyUnavailableException)
 | KeyManagementService_KMSInternalException(KMSInternalException: KMSInternalException)
 | KeyManagementService_KMSInvalidSignatureException(KMSInvalidSignatureException: KMSInvalidSignatureException)
 | KeyManagementService_KMSInvalidStateException(KMSInvalidStateException: KMSInvalidStateException)
 | KeyManagementService_LimitExceededException(LimitExceededException: LimitExceededException)
 | KeyManagementService_MalformedPolicyDocumentException(MalformedPolicyDocumentException: MalformedPolicyDocumentException)
 | KeyManagementService_NotFoundException(NotFoundException: NotFoundException)
 | KeyManagementService_TagException(TagException: TagException)
 | KeyManagementService_UnsupportedOperationException(UnsupportedOperationException: UnsupportedOperationException)
 function method CastKeyManagementServiceErrorToString(error: KeyManagementServiceError): string {
 	match error
	case KeyManagementService_AlreadyExistsException(arg) => arg.CastToString()
	case KeyManagementService_CloudHsmClusterInUseException(arg) => arg.CastToString()
	case KeyManagementService_CloudHsmClusterInvalidConfigurationException(arg) => arg.CastToString()
	case KeyManagementService_CloudHsmClusterNotActiveException(arg) => arg.CastToString()
	case KeyManagementService_CloudHsmClusterNotFoundException(arg) => arg.CastToString()
	case KeyManagementService_CloudHsmClusterNotRelatedException(arg) => arg.CastToString()
	case KeyManagementService_CustomKeyStoreHasCMKsException(arg) => arg.CastToString()
	case KeyManagementService_CustomKeyStoreInvalidStateException(arg) => arg.CastToString()
	case KeyManagementService_CustomKeyStoreNameInUseException(arg) => arg.CastToString()
	case KeyManagementService_CustomKeyStoreNotFoundException(arg) => arg.CastToString()
	case KeyManagementService_DependencyTimeoutException(arg) => arg.CastToString()
	case KeyManagementService_DisabledException(arg) => arg.CastToString()
	case KeyManagementService_ExpiredImportTokenException(arg) => arg.CastToString()
	case KeyManagementService_IncorrectKeyException(arg) => arg.CastToString()
	case KeyManagementService_IncorrectKeyMaterialException(arg) => arg.CastToString()
	case KeyManagementService_IncorrectTrustAnchorException(arg) => arg.CastToString()
	case KeyManagementService_InvalidAliasNameException(arg) => arg.CastToString()
	case KeyManagementService_InvalidArnException(arg) => arg.CastToString()
	case KeyManagementService_InvalidCiphertextException(arg) => arg.CastToString()
	case KeyManagementService_InvalidGrantIdException(arg) => arg.CastToString()
	case KeyManagementService_InvalidGrantTokenException(arg) => arg.CastToString()
	case KeyManagementService_InvalidImportTokenException(arg) => arg.CastToString()
	case KeyManagementService_InvalidKeyUsageException(arg) => arg.CastToString()
	case KeyManagementService_InvalidMarkerException(arg) => arg.CastToString()
	case KeyManagementService_KeyUnavailableException(arg) => arg.CastToString()
	case KeyManagementService_KMSInternalException(arg) => arg.CastToString()
	case KeyManagementService_KMSInvalidSignatureException(arg) => arg.CastToString()
	case KeyManagementService_KMSInvalidStateException(arg) => arg.CastToString()
	case KeyManagementService_LimitExceededException(arg) => arg.CastToString()
	case KeyManagementService_MalformedPolicyDocumentException(arg) => arg.CastToString()
	case KeyManagementService_NotFoundException(arg) => arg.CastToString()
	case KeyManagementService_TagException(arg) => arg.CastToString()
	case KeyManagementService_UnsupportedOperationException(arg) => arg.CastToString()
	case _ => "Unexpected Exception from AWS KeyManagementService"
}
 datatype KeyManagerType =
	| AWS
	| CUSTOMER
 datatype KeyMetadata = KeyMetadata (
	nameonly AWSAccountId: Option<AWSAccountIdType> ,
	nameonly KeyId: KeyIdType ,
	nameonly Arn: Option<ArnType> ,
	nameonly CreationDate: Option<string> ,
	nameonly Enabled: Option<BooleanType> ,
	nameonly Description: Option<DescriptionType> ,
	nameonly KeyUsage: Option<KeyUsageType> ,
	nameonly KeyState: Option<KeyState> ,
	nameonly DeletionDate: Option<string> ,
	nameonly ValidTo: Option<string> ,
	nameonly Origin: Option<OriginType> ,
	nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
	nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> ,
	nameonly ExpirationModel: Option<ExpirationModelType> ,
	nameonly KeyManager: Option<KeyManagerType> ,
	nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
	nameonly KeySpec: Option<KeySpec> ,
	nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> ,
	nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> ,
	nameonly MultiRegion: Option<NullableBooleanType> ,
	nameonly MultiRegionConfiguration: Option<MultiRegionConfiguration> ,
	nameonly PendingDeletionWindowInDays: Option<PendingWindowInDaysType> )
 datatype KeySpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
	| SYMMETRIC_DEFAULT
 datatype KeyState =
	| Creating
	| Enabled
	| Disabled
	| PendingDeletion
	| PendingImport
	| PendingReplicaDeletion
	| Unavailable
	| Updating
 type KeyStorePasswordType = x: string |  ( 7 <= |x| <= 32 ) witness *
 datatype KeyUnavailableException = KeyUnavailableException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "KeyUnavailableException: " + message.value else "KeyUnavailableException"
	}
 }
 datatype KeyUsageType =
	| SIGN_VERIFY
	| ENCRYPT_DECRYPT
 datatype KMSInternalException = KMSInternalException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "KMSInternalException: " + message.value else "KMSInternalException"
	}
 }
 datatype KMSInvalidSignatureException = KMSInvalidSignatureException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "KMSInvalidSignatureException: " + message.value else "KMSInvalidSignatureException"
	}
 }
 datatype KMSInvalidStateException = KMSInvalidStateException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "KMSInvalidStateException: " + message.value else "KMSInvalidStateException"
	}
 }
 datatype LimitExceededException = LimitExceededException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "LimitExceededException: " + message.value else "LimitExceededException"
	}
 }
 type LimitType = x: int32 |  ( 1 <= x <= 1000 ) witness *
 datatype ListAliasesRequest = ListAliasesRequest (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> )
 datatype ListAliasesResponse = ListAliasesResponse (
	nameonly Aliases: Option<AliasList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
 datatype ListGrantsRequest = ListGrantsRequest (
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> ,
	nameonly KeyId: KeyIdType ,
	nameonly GrantId: Option<GrantIdType> ,
	nameonly GranteePrincipal: Option<PrincipalIdType> )
 datatype ListGrantsResponse = ListGrantsResponse (
	nameonly Grants: Option<GrantList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
 datatype ListKeyPoliciesRequest = ListKeyPoliciesRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> )
 datatype ListKeyPoliciesResponse = ListKeyPoliciesResponse (
	nameonly PolicyNames: Option<PolicyNameList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
 datatype ListKeysRequest = ListKeysRequest (
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> )
 datatype ListResourceTagsRequest = ListResourceTagsRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> )
 datatype ListResourceTagsResponse = ListResourceTagsResponse (
	nameonly Tags: Option<TagList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
 datatype ListRetirableGrantsRequest = ListRetirableGrantsRequest (
	nameonly Limit: Option<LimitType> ,
	nameonly Marker: Option<MarkerType> ,
	nameonly RetiringPrincipal: PrincipalIdType )
 datatype MalformedPolicyDocumentException = MalformedPolicyDocumentException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "MalformedPolicyDocumentException: " + message.value else "MalformedPolicyDocumentException"
	}
 }
 type MarkerType = x: string |  ( 1 <= |x| <= 1024 ) witness *
 datatype MessageType =
	| RAW
	| DIGEST
 datatype MultiRegionConfiguration = MultiRegionConfiguration (
	nameonly MultiRegionKeyType: Option<MultiRegionKeyType> ,
	nameonly PrimaryKey: Option<MultiRegionKey> ,
	nameonly ReplicaKeys: Option<MultiRegionKeyList> )
 datatype MultiRegionKey = MultiRegionKey (
	nameonly Arn: Option<ArnType> ,
	nameonly Region: Option<RegionType> )
 type MultiRegionKeyList = seq<MultiRegionKey>
 datatype MultiRegionKeyType =
	| PRIMARY
	| REPLICA
 datatype NotFoundException = NotFoundException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "NotFoundException: " + message.value else "NotFoundException"
	}
 }
 type NullableBooleanType = bool
 type NumberOfBytesType = x: int32 |  ( 1 <= x <= 1024 ) witness *
 datatype OriginType =
	| AWS_KMS
	| EXTERNAL
	| AWS_CLOUDHSM
 type PendingWindowInDaysType = x: int32 |  ( 1 <= x <= 365 ) witness *
 type PlaintextType = x: seq<uint8> |  ( 1 <= |x| <= 4096 ) witness *
 type PolicyNameList = seq<PolicyNameType>
 type PolicyNameType = x: string |  ( 1 <= |x| <= 128 ) witness *
 type PolicyType = x: string |  ( 1 <= |x| <= 131072 ) witness *
 type PrincipalIdType = x: string |  ( 1 <= |x| <= 256 ) witness *
 type PublicKeyType = x: seq<uint8> |  ( 1 <= |x| <= 8192 ) witness *
 datatype PutKeyPolicyRequest = PutKeyPolicyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly PolicyName: PolicyNameType ,
	nameonly Policy: PolicyType ,
	nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> )
 datatype ReEncryptRequest = ReEncryptRequest (
	nameonly CiphertextBlob: CiphertextType ,
	nameonly SourceEncryptionContext: Option<EncryptionContextType> ,
	nameonly SourceKeyId: Option<KeyIdType> ,
	nameonly DestinationKeyId: KeyIdType ,
	nameonly DestinationEncryptionContext: Option<EncryptionContextType> ,
	nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
	nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype ReEncryptResponse = ReEncryptResponse (
	nameonly CiphertextBlob: Option<CiphertextType> ,
	nameonly SourceKeyId: Option<KeyIdType> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
	nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> )
 type RegionType = x: string |  ( 1 <= |x| <= 32 ) witness *
 datatype ReplicateKeyRequest = ReplicateKeyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly ReplicaRegion: RegionType ,
	nameonly Policy: Option<PolicyType> ,
	nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> ,
	nameonly Description: Option<DescriptionType> ,
	nameonly Tags: Option<TagList> )
 datatype ReplicateKeyResponse = ReplicateKeyResponse (
	nameonly ReplicaKeyMetadata: Option<KeyMetadata> ,
	nameonly ReplicaPolicy: Option<PolicyType> ,
	nameonly ReplicaTags: Option<TagList> )
 datatype RetireGrantRequest = RetireGrantRequest (
	nameonly GrantToken: Option<GrantTokenType> ,
	nameonly KeyId: Option<KeyIdType> ,
	nameonly GrantId: Option<GrantIdType> )
 datatype RevokeGrantRequest = RevokeGrantRequest (
	nameonly KeyId: KeyIdType ,
	nameonly GrantId: GrantIdType )
 datatype ScheduleKeyDeletionRequest = ScheduleKeyDeletionRequest (
	nameonly KeyId: KeyIdType ,
	nameonly PendingWindowInDays: Option<PendingWindowInDaysType> )
 datatype ScheduleKeyDeletionResponse = ScheduleKeyDeletionResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly DeletionDate: Option<string> ,
	nameonly KeyState: Option<KeyState> ,
	nameonly PendingWindowInDays: Option<PendingWindowInDaysType> )
 datatype SigningAlgorithmSpec =
	| RSASSA_PSS_SHA_256
	| RSASSA_PSS_SHA_384
	| RSASSA_PSS_SHA_512
	| RSASSA_PKCS1_V1_5_SHA_256
	| RSASSA_PKCS1_V1_5_SHA_384
	| RSASSA_PKCS1_V1_5_SHA_512
	| ECDSA_SHA_256
	| ECDSA_SHA_384
	| ECDSA_SHA_512
 type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>
 datatype SignRequest = SignRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Message: PlaintextType ,
	nameonly MessageType: Option<MessageType> ,
	nameonly GrantTokens: Option<GrantTokenList> ,
	nameonly SigningAlgorithm: SigningAlgorithmSpec )
 datatype SignResponse = SignResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly Signature: Option<CiphertextType> ,
	nameonly SigningAlgorithm: Option<SigningAlgorithmSpec> )
 datatype Tag = Tag (
	nameonly TagKey: TagKeyType ,
	nameonly TagValue: TagValueType )
 datatype TagException = TagException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "TagException: " + message.value else "TagException"
	}
 }
 type TagKeyList = seq<TagKeyType>
 type TagKeyType = x: string |  ( 1 <= |x| <= 128 ) witness *
 type TagList = seq<Tag>
 datatype TagResourceRequest = TagResourceRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Tags: TagList )
 type TagValueType = x: string |  ( 0 <= |x| <= 256 ) witness *
 type TrustAnchorCertificateType = x: string |  ( 1 <= |x| <= 5000 ) witness *
 datatype UnsupportedOperationException = UnsupportedOperationException (
	nameonly message: Option<ErrorMessageType> ) {
 	function method CastToString(): string {
		if message.Some? then "UnsupportedOperationException: " + message.value else "UnsupportedOperationException"
	}
 }
 datatype UntagResourceRequest = UntagResourceRequest (
	nameonly KeyId: KeyIdType ,
	nameonly TagKeys: TagKeyList )
 datatype UpdateAliasRequest = UpdateAliasRequest (
	nameonly AliasName: AliasNameType ,
	nameonly TargetKeyId: KeyIdType )
 datatype UpdateCustomKeyStoreRequest = UpdateCustomKeyStoreRequest (
	nameonly CustomKeyStoreId: CustomKeyStoreIdType ,
	nameonly NewCustomKeyStoreName: Option<CustomKeyStoreNameType> ,
	nameonly KeyStorePassword: Option<KeyStorePasswordType> ,
	nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> )
 datatype UpdateCustomKeyStoreResponse = UpdateCustomKeyStoreResponse (  )
 datatype UpdateKeyDescriptionRequest = UpdateKeyDescriptionRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Description: DescriptionType )
 datatype UpdatePrimaryRegionRequest = UpdatePrimaryRegionRequest (
	nameonly KeyId: KeyIdType ,
	nameonly PrimaryRegion: RegionType )
 datatype VerifyRequest = VerifyRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Message: PlaintextType ,
	nameonly MessageType: Option<MessageType> ,
	nameonly Signature: CiphertextType ,
	nameonly SigningAlgorithm: SigningAlgorithmSpec ,
	nameonly GrantTokens: Option<GrantTokenList> )
 datatype VerifyResponse = VerifyResponse (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly SignatureValid: Option<BooleanType> ,
	nameonly SigningAlgorithm: Option<SigningAlgorithmSpec> )
 datatype WrappingKeySpec =
	| RSA_2048
}