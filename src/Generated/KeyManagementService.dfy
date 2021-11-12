// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-11T16:21:55.383509
include "../StandardLibrary/StandardLibrary.dfy"
 module {:extern "Dafny.Com.Amazonaws.Kms.KeyManagementService"} Com.Amazonaws.Kms.KeyManagementService {
 import opened Wrappers
import opened StandardLibrary.UInt
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
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
 datatype CloudHsmClusterInvalidConfigurationException = CloudHsmClusterInvalidConfigurationException (
	nameonly message: Option<ErrorMessageType> )
 datatype CloudHsmClusterNotActiveException = CloudHsmClusterNotActiveException (
	nameonly message: Option<ErrorMessageType> )
 datatype CloudHsmClusterNotFoundException = CloudHsmClusterNotFoundException (
	nameonly message: Option<ErrorMessageType> )
 datatype CloudHsmClusterNotRelatedException = CloudHsmClusterNotRelatedException (
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
 type CustomKeyStoreIdType = x: string |  ( 1 <= |x| <= 64 ) witness *
 datatype CustomKeyStoreInvalidStateException = CustomKeyStoreInvalidStateException (
	nameonly message: Option<ErrorMessageType> )
 datatype CustomKeyStoreNameInUseException = CustomKeyStoreNameInUseException (
	nameonly message: Option<ErrorMessageType> )
 type CustomKeyStoreNameType = x: string |  ( 1 <= |x| <= 256 ) witness *
 datatype CustomKeyStoreNotFoundException = CustomKeyStoreNotFoundException (
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
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
 type EncryptionContextKey = string
 type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>
 type EncryptionContextValue = string
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
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
 datatype IncorrectKeyMaterialException = IncorrectKeyMaterialException (
	nameonly message: Option<ErrorMessageType> )
 datatype IncorrectTrustAnchorException = IncorrectTrustAnchorException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidAliasNameException = InvalidAliasNameException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidArnException = InvalidArnException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidCiphertextException = InvalidCiphertextException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidGrantIdException = InvalidGrantIdException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidGrantTokenException = InvalidGrantTokenException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidImportTokenException = InvalidImportTokenException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidKeyUsageException = InvalidKeyUsageException (
	nameonly message: Option<ErrorMessageType> )
 datatype InvalidMarkerException = InvalidMarkerException (
	nameonly message: Option<ErrorMessageType> )
 type KeyIdType = x: string |  ( 1 <= |x| <= 2048 ) witness *
 type KeyList = seq<KeyListEntry>
 datatype KeyListEntry = KeyListEntry (
	nameonly KeyId: Option<KeyIdType> ,
	nameonly KeyArn: Option<ArnType> )
 trait IKeyManagementServiceClient {
 method CancelKeyDeletion ( input: CancelKeyDeletionRequest ) returns (output: Result<CancelKeyDeletionResponse, KeyManagementServiceError>)
 method ConnectCustomKeyStore ( input: ConnectCustomKeyStoreRequest ) returns (output: Result<ConnectCustomKeyStoreResponse, KeyManagementServiceError>)
 method CreateAlias ( input: CreateAliasRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method CreateCustomKeyStore ( input: CreateCustomKeyStoreRequest ) returns (output: Result<CreateCustomKeyStoreResponse, KeyManagementServiceError>)
 method CreateGrant ( input: CreateGrantRequest ) returns (output: Result<CreateGrantResponse, KeyManagementServiceError>)
 method CreateKey ( input: CreateKeyRequest ) returns (output: Result<CreateKeyResponse, KeyManagementServiceError>)
 method Decrypt ( input: DecryptRequest ) returns (output: Result<DecryptResponse, KeyManagementServiceError>)
 method DeleteAlias ( input: DeleteAliasRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method DeleteCustomKeyStore ( input: DeleteCustomKeyStoreRequest ) returns (output: Result<DeleteCustomKeyStoreResponse, KeyManagementServiceError>)
 method DeleteImportedKeyMaterial ( input: DeleteImportedKeyMaterialRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method DescribeCustomKeyStores ( input: DescribeCustomKeyStoresRequest ) returns (output: Result<DescribeCustomKeyStoresResponse, KeyManagementServiceError>)
 method DescribeKey ( input: DescribeKeyRequest ) returns (output: Result<DescribeKeyResponse, KeyManagementServiceError>)
 method DisableKey ( input: DisableKeyRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method DisableKeyRotation ( input: DisableKeyRotationRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method DisconnectCustomKeyStore ( input: DisconnectCustomKeyStoreRequest ) returns (output: Result<DisconnectCustomKeyStoreResponse, KeyManagementServiceError>)
 method EnableKey ( input: EnableKeyRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method EnableKeyRotation ( input: EnableKeyRotationRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method Encrypt ( input: EncryptRequest ) returns (output: Result<EncryptResponse, KeyManagementServiceError>)
 method GenerateDataKey ( input: GenerateDataKeyRequest ) returns (output: Result<GenerateDataKeyResponse, KeyManagementServiceError>)
 method GenerateDataKeyPair ( input: GenerateDataKeyPairRequest ) returns (output: Result<GenerateDataKeyPairResponse, KeyManagementServiceError>)
 method GenerateDataKeyPairWithoutPlaintext ( input: GenerateDataKeyPairWithoutPlaintextRequest ) returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, KeyManagementServiceError>)
 method GenerateDataKeyWithoutPlaintext ( input: GenerateDataKeyWithoutPlaintextRequest ) returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, KeyManagementServiceError>)
 method GenerateRandom ( input: GenerateRandomRequest ) returns (output: Result<GenerateRandomResponse, KeyManagementServiceError>)
 method GetKeyPolicy ( input: GetKeyPolicyRequest ) returns (output: Result<GetKeyPolicyResponse, KeyManagementServiceError>)
 method GetKeyRotationStatus ( input: GetKeyRotationStatusRequest ) returns (output: Result<GetKeyRotationStatusResponse, KeyManagementServiceError>)
 method GetParametersForImport ( input: GetParametersForImportRequest ) returns (output: Result<GetParametersForImportResponse, KeyManagementServiceError>)
 method GetPublicKey ( input: GetPublicKeyRequest ) returns (output: Result<GetPublicKeyResponse, KeyManagementServiceError>)
 method ImportKeyMaterial ( input: ImportKeyMaterialRequest ) returns (output: Result<ImportKeyMaterialResponse, KeyManagementServiceError>)
 method ListAliases ( input: ListAliasesRequest ) returns (output: Result<ListAliasesResponse, KeyManagementServiceError>)
 method ListGrants ( input: ListGrantsRequest ) returns (output: Result<ListGrantsResponse, KeyManagementServiceError>)
 method ListKeyPolicies ( input: ListKeyPoliciesRequest ) returns (output: Result<ListKeyPoliciesResponse, KeyManagementServiceError>)
 method ListKeys ( input: ListKeysRequest ) returns (output: Result<ListKeysResponse, KeyManagementServiceError>)
 method ListResourceTags ( input: ListResourceTagsRequest ) returns (output: Result<ListResourceTagsResponse, KeyManagementServiceError>)
 method ListRetirableGrants ( input: ListRetirableGrantsRequest ) returns (output: Result<ListGrantsResponse, KeyManagementServiceError>)
 method PutKeyPolicy ( input: PutKeyPolicyRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method ReEncrypt ( input: ReEncryptRequest ) returns (output: Result<ReEncryptResponse, KeyManagementServiceError>)
 method ReplicateKey ( input: ReplicateKeyRequest ) returns (output: Result<ReplicateKeyResponse, KeyManagementServiceError>)
 method RetireGrant ( input: RetireGrantRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method RevokeGrant ( input: RevokeGrantRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method ScheduleKeyDeletion ( input: ScheduleKeyDeletionRequest ) returns (output: Result<ScheduleKeyDeletionResponse, KeyManagementServiceError>)
 method Sign ( input: SignRequest ) returns (output: Result<SignResponse, KeyManagementServiceError>)
 method TagResource ( input: TagResourceRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method UntagResource ( input: UntagResourceRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method UpdateAlias ( input: UpdateAliasRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method UpdateCustomKeyStore ( input: UpdateCustomKeyStoreRequest ) returns (output: Result<UpdateCustomKeyStoreResponse, KeyManagementServiceError>)
 method UpdateKeyDescription ( input: UpdateKeyDescriptionRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method UpdatePrimaryRegion ( input: UpdatePrimaryRegionRequest ) returns (output: Result<(), KeyManagementServiceError>)
 method Verify ( input: VerifyRequest ) returns (output: Result<VerifyResponse, KeyManagementServiceError>)
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
	nameonly message: Option<ErrorMessageType> )
 datatype KeyUsageType =
	| SIGN_VERIFY
	| ENCRYPT_DECRYPT
 datatype KMSInternalException = KMSInternalException (
	nameonly message: Option<ErrorMessageType> )
 datatype KMSInvalidSignatureException = KMSInvalidSignatureException (
	nameonly message: Option<ErrorMessageType> )
 datatype KMSInvalidStateException = KMSInvalidStateException (
	nameonly message: Option<ErrorMessageType> )
 datatype LimitExceededException = LimitExceededException (
	nameonly message: Option<ErrorMessageType> )
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
 datatype ListKeysResponse = ListKeysResponse (
	nameonly Keys: Option<KeyList> ,
	nameonly NextMarker: Option<MarkerType> ,
	nameonly Truncated: Option<BooleanType> )
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
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
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
	nameonly message: Option<ErrorMessageType> )
 type TagKeyList = seq<TagKeyType>
 type TagKeyType = x: string |  ( 1 <= |x| <= 128 ) witness *
 type TagList = seq<Tag>
 datatype TagResourceRequest = TagResourceRequest (
	nameonly KeyId: KeyIdType ,
	nameonly Tags: TagList )
 type TagValueType = x: string |  ( 0 <= |x| <= 256 ) witness *
 type TrustAnchorCertificateType = x: string |  ( 1 <= |x| <= 5000 ) witness *
 datatype UnsupportedOperationException = UnsupportedOperationException (
	nameonly message: Option<ErrorMessageType> )
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