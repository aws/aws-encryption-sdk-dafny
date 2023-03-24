// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/src/Index.dfy"
 include "../../AwsCryptographyPrimitives/src/Index.dfy"
 include "../../ComAmazonawsDynamodb/src/Index.dfy"
 include "../../ComAmazonawsKms/src/Index.dfy"
 module {:extern "Dafny.Aws.Cryptography.MaterialProviders.Types" } AwsCryptographyMaterialProvidersTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import AwsCryptographyPrimitivesTypes
 import ComAmazonawsDynamodbTypes
 import ComAmazonawsKmsTypes
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 type AccountId = string
 type AccountIdList = seq<AccountId>
 datatype AesWrappingAlg =
	| ALG_AES128_GCM_IV12_TAG16
	| ALG_AES192_GCM_IV12_TAG16
	| ALG_AES256_GCM_IV12_TAG16
 datatype AlgorithmSuiteId =
 | ESDK(ESDK: ESDKAlgorithmSuiteId)
 | DBE(DBE: DBEAlgorithmSuiteId)
 datatype AlgorithmSuiteInfo = | AlgorithmSuiteInfo (
 nameonly id: AlgorithmSuiteId ,
 nameonly binaryId: seq<uint8> ,
 nameonly messageVersion: int32 ,
 nameonly encrypt: Encrypt ,
 nameonly kdf: DerivationAlgorithm ,
 nameonly commitment: DerivationAlgorithm ,
 nameonly signature: SignatureAlgorithm ,
 nameonly symmetricSignature: SymmetricSignatureAlgorithm ,
 nameonly edkWrapping: EdkWrappingAlgorithm
 )
 class IAwsCryptographicMaterialProvidersClientCallHistory {
 ghost constructor() {
 CreateAwsKmsKeyring := [];
 CreateAwsKmsDiscoveryKeyring := [];
 CreateAwsKmsMultiKeyring := [];
 CreateAwsKmsDiscoveryMultiKeyring := [];
 CreateAwsKmsMrkKeyring := [];
 CreateAwsKmsMrkMultiKeyring := [];
 CreateAwsKmsMrkDiscoveryKeyring := [];
 CreateAwsKmsMrkDiscoveryMultiKeyring := [];
 CreateAwsKmsHierarchicalKeyring := [];
 CreateMultiKeyring := [];
 CreateRawAesKeyring := [];
 CreateRawRsaKeyring := [];
 CreateAwsKmsRsaKeyring := [];
 CreateDefaultCryptographicMaterialsManager := [];
 CreateExpectedEncryptionContextCMM := [];
 CreateCryptographicMaterialsCache := [];
 CreateDefaultClientSupplier := [];
 InitializeEncryptionMaterials := [];
 InitializeDecryptionMaterials := [];
 ValidEncryptionMaterialsTransition := [];
 ValidDecryptionMaterialsTransition := [];
 EncryptionMaterialsHasPlaintextDataKey := [];
 DecryptionMaterialsWithPlaintextDataKey := [];
 GetAlgorithmSuiteInfo := [];
 ValidAlgorithmSuiteInfo := [];
 ValidateCommitmentPolicyOnEncrypt := [];
 ValidateCommitmentPolicyOnDecrypt := [];
}
 ghost var CreateAwsKmsKeyring: seq<DafnyCallEvent<CreateAwsKmsKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsDiscoveryKeyring: seq<DafnyCallEvent<CreateAwsKmsDiscoveryKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsMultiKeyring: seq<DafnyCallEvent<CreateAwsKmsMultiKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsDiscoveryMultiKeyring: seq<DafnyCallEvent<CreateAwsKmsDiscoveryMultiKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsMrkKeyring: seq<DafnyCallEvent<CreateAwsKmsMrkKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsMrkMultiKeyring: seq<DafnyCallEvent<CreateAwsKmsMrkMultiKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsMrkDiscoveryKeyring: seq<DafnyCallEvent<CreateAwsKmsMrkDiscoveryKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsMrkDiscoveryMultiKeyring: seq<DafnyCallEvent<CreateAwsKmsMrkDiscoveryMultiKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsHierarchicalKeyring: seq<DafnyCallEvent<CreateAwsKmsHierarchicalKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateMultiKeyring: seq<DafnyCallEvent<CreateMultiKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateRawAesKeyring: seq<DafnyCallEvent<CreateRawAesKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateRawRsaKeyring: seq<DafnyCallEvent<CreateRawRsaKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateAwsKmsRsaKeyring: seq<DafnyCallEvent<CreateAwsKmsRsaKeyringInput, Result<IKeyring, Error>>>
 ghost var CreateDefaultCryptographicMaterialsManager: seq<DafnyCallEvent<CreateDefaultCryptographicMaterialsManagerInput, Result<ICryptographicMaterialsManager, Error>>>
 ghost var CreateExpectedEncryptionContextCMM: seq<DafnyCallEvent<CreateExpectedEncryptionContextCMMInput, Result<ICryptographicMaterialsManager, Error>>>
 ghost var CreateCryptographicMaterialsCache: seq<DafnyCallEvent<CreateCryptographicMaterialsCacheInput, Result<ICryptographicMaterialsCache, Error>>>
 ghost var CreateDefaultClientSupplier: seq<DafnyCallEvent<CreateDefaultClientSupplierInput, Result<IClientSupplier, Error>>>
 ghost var InitializeEncryptionMaterials: seq<DafnyCallEvent<InitializeEncryptionMaterialsInput, Result<EncryptionMaterials, Error>>>
 ghost var InitializeDecryptionMaterials: seq<DafnyCallEvent<InitializeDecryptionMaterialsInput, Result<DecryptionMaterials, Error>>>
 ghost var ValidEncryptionMaterialsTransition: seq<DafnyCallEvent<ValidEncryptionMaterialsTransitionInput, Result<(), Error>>>
 ghost var ValidDecryptionMaterialsTransition: seq<DafnyCallEvent<ValidDecryptionMaterialsTransitionInput, Result<(), Error>>>
 ghost var EncryptionMaterialsHasPlaintextDataKey: seq<DafnyCallEvent<EncryptionMaterials, Result<(), Error>>>
 ghost var DecryptionMaterialsWithPlaintextDataKey: seq<DafnyCallEvent<DecryptionMaterials, Result<(), Error>>>
 ghost var GetAlgorithmSuiteInfo: seq<DafnyCallEvent<seq<uint8>, Result<AlgorithmSuiteInfo, Error>>>
 ghost var ValidAlgorithmSuiteInfo: seq<DafnyCallEvent<AlgorithmSuiteInfo, Result<(), Error>>>
 ghost var ValidateCommitmentPolicyOnEncrypt: seq<DafnyCallEvent<ValidateCommitmentPolicyOnEncryptInput, Result<(), Error>>>
 ghost var ValidateCommitmentPolicyOnDecrypt: seq<DafnyCallEvent<ValidateCommitmentPolicyOnDecryptInput, Result<(), Error>>>
}
 trait {:termination false} IAwsCryptographicMaterialProvidersClient
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IAwsCryptographicMaterialProvidersClientCallHistory
 predicate CreateAwsKmsKeyringEnsuresPublicly(input: CreateAwsKmsKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsKeyring ( input: CreateAwsKmsKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsKeyring == old(History.CreateAwsKmsKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsDiscoveryKeyring ( input: CreateAwsKmsDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsDiscoveryKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsDiscoveryKeyring == old(History.CreateAwsKmsDiscoveryKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsMultiKeyringEnsuresPublicly(input: CreateAwsKmsMultiKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsMultiKeyring ( input: CreateAwsKmsMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMultiKeyring == old(History.CreateAwsKmsMultiKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsDiscoveryMultiKeyring ( input: CreateAwsKmsDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsDiscoveryMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsDiscoveryMultiKeyring == old(History.CreateAwsKmsDiscoveryMultiKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsMrkKeyringEnsuresPublicly(input: CreateAwsKmsMrkKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsMrkKeyring ( input: CreateAwsKmsMrkKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsMrkKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkKeyring == old(History.CreateAwsKmsMrkKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkMultiKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsMrkMultiKeyring ( input: CreateAwsKmsMrkMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMrkMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkMultiKeyring == old(History.CreateAwsKmsMrkMultiKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsMrkDiscoveryKeyring ( input: CreateAwsKmsMrkDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsMrkDiscoveryKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkDiscoveryKeyring == old(History.CreateAwsKmsMrkDiscoveryKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsMrkDiscoveryMultiKeyring ( input: CreateAwsKmsMrkDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMrkDiscoveryMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkDiscoveryMultiKeyring == old(History.CreateAwsKmsMrkDiscoveryMultiKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input: CreateAwsKmsHierarchicalKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsHierarchicalKeyring ( input: CreateAwsKmsHierarchicalKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.branchKeyIdSupplier.Some? ==>
 && input.branchKeyIdSupplier.value.ValidState()
 && input.branchKeyIdSupplier.value.Modifies !! {History}
 )
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 && input.ddbClient.ValidState()
 && input.ddbClient.Modifies !! {History}
 modifies Modifies - {History} ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies ,
 History`CreateAwsKmsHierarchicalKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) - input.kmsClient.Modifies - input.ddbClient.Modifies ) )
 ensures CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsHierarchicalKeyring == old(History.CreateAwsKmsHierarchicalKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateMultiKeyringEnsuresPublicly(input: CreateMultiKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateMultiKeyring ( input: CreateMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.generator.Some? ==>
 && input.generator.value.ValidState()
 && input.generator.value.Modifies !! {History}
 ) && ( forall i <- input.childKeyrings ::
 && i.ValidState()
 && i.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m) ,
 History`CreateMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m)
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.generator.Some? then input.generator.value.Modifies else {}) - (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m) ) )
 ensures CreateMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateMultiKeyring == old(History.CreateMultiKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateRawAesKeyringEnsuresPublicly(input: CreateRawAesKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateRawAesKeyring ( input: CreateRawAesKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateRawAesKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateRawAesKeyringEnsuresPublicly(input, output)
 ensures History.CreateRawAesKeyring == old(History.CreateRawAesKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateRawRsaKeyringEnsuresPublicly(input: CreateRawRsaKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateRawRsaKeyring ( input: CreateRawRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateRawRsaKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateRawRsaKeyringEnsuresPublicly(input, output)
 ensures History.CreateRawRsaKeyring == old(History.CreateRawRsaKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateAwsKmsRsaKeyringEnsuresPublicly(input: CreateAwsKmsRsaKeyringInput , output: Result<IKeyring, Error>)
 // The public method to be called by library consumers
 method CreateAwsKmsRsaKeyring ( input: CreateAwsKmsRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.kmsClient.Some? ==>
 && input.kmsClient.value.ValidState()
 && input.kmsClient.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {}) ,
 History`CreateAwsKmsRsaKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {}) ) )
 ensures CreateAwsKmsRsaKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsRsaKeyring == old(History.CreateAwsKmsRsaKeyring) + [DafnyCallEvent(input, output)]
 
 predicate CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input: CreateDefaultCryptographicMaterialsManagerInput , output: Result<ICryptographicMaterialsManager, Error>)
 // The public method to be called by library consumers
 method CreateDefaultCryptographicMaterialsManager ( input: CreateDefaultCryptographicMaterialsManagerInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidState()
 && input.keyring.ValidState()
 && input.keyring.Modifies !! {History}
 modifies Modifies - {History} ,
 input.keyring.Modifies ,
 History`CreateDefaultCryptographicMaterialsManager
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.keyring.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.keyring.Modifies ) )
 ensures CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input, output)
 ensures History.CreateDefaultCryptographicMaterialsManager == old(History.CreateDefaultCryptographicMaterialsManager) + [DafnyCallEvent(input, output)]
 
 predicate CreateExpectedEncryptionContextCMMEnsuresPublicly(input: CreateExpectedEncryptionContextCMMInput , output: Result<ICryptographicMaterialsManager, Error>)
 // The public method to be called by library consumers
 method CreateExpectedEncryptionContextCMM ( input: CreateExpectedEncryptionContextCMMInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidState() && ( input.underlyingCMM.Some? ==>
 && input.underlyingCMM.value.ValidState()
 && input.underlyingCMM.value.Modifies !! {History}
 ) && ( input.keyring.Some? ==>
 && input.keyring.value.ValidState()
 && input.keyring.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {}) ,
 History`CreateExpectedEncryptionContextCMM
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) - (if input.keyring.Some? then input.keyring.value.Modifies else {}) ) )
 ensures CreateExpectedEncryptionContextCMMEnsuresPublicly(input, output)
 ensures History.CreateExpectedEncryptionContextCMM == old(History.CreateExpectedEncryptionContextCMM) + [DafnyCallEvent(input, output)]
 
 predicate CreateCryptographicMaterialsCacheEnsuresPublicly(input: CreateCryptographicMaterialsCacheInput , output: Result<ICryptographicMaterialsCache, Error>)
 // The public method to be called by library consumers
 method CreateCryptographicMaterialsCache ( input: CreateCryptographicMaterialsCacheInput )
 returns (output: Result<ICryptographicMaterialsCache, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateCryptographicMaterialsCache
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateCryptographicMaterialsCacheEnsuresPublicly(input, output)
 ensures History.CreateCryptographicMaterialsCache == old(History.CreateCryptographicMaterialsCache) + [DafnyCallEvent(input, output)]
 
 predicate CreateDefaultClientSupplierEnsuresPublicly(input: CreateDefaultClientSupplierInput , output: Result<IClientSupplier, Error>)
 // The public method to be called by library consumers
 method CreateDefaultClientSupplier ( input: CreateDefaultClientSupplierInput )
 returns (output: Result<IClientSupplier, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateDefaultClientSupplier
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateDefaultClientSupplierEnsuresPublicly(input, output)
 ensures History.CreateDefaultClientSupplier == old(History.CreateDefaultClientSupplier) + [DafnyCallEvent(input, output)]
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method InitializeEncryptionMaterials ( input: InitializeEncryptionMaterialsInput )
 : (output: Result<EncryptionMaterials, Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method InitializeDecryptionMaterials ( input: InitializeDecryptionMaterialsInput )
 : (output: Result<DecryptionMaterials, Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method ValidEncryptionMaterialsTransition ( input: ValidEncryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method ValidDecryptionMaterialsTransition ( input: ValidDecryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method EncryptionMaterialsHasPlaintextDataKey ( input: EncryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method DecryptionMaterialsWithPlaintextDataKey ( input: DecryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method GetAlgorithmSuiteInfo ( input: seq<uint8> )
 : (output: Result<AlgorithmSuiteInfo, Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method ValidAlgorithmSuiteInfo ( input: AlgorithmSuiteInfo )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method ValidateCommitmentPolicyOnEncrypt ( input: ValidateCommitmentPolicyOnEncryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
 // Functions are deterministic, no need for historical call events or ensures indirection
 // The public method to be called by library consumers
 function method ValidateCommitmentPolicyOnDecrypt ( input: ValidateCommitmentPolicyOnDecryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 
}
 class IBranchKeyIdSupplierCallHistory {
 ghost constructor() {
 GetBranchKeyId := [];
}
 ghost var GetBranchKeyId: seq<DafnyCallEvent<GetBranchKeyIdInput, Result<GetBranchKeyIdOutput, Error>>>
}
 trait {:termination false} IBranchKeyIdSupplier
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IBranchKeyIdSupplierCallHistory
 predicate GetBranchKeyIdEnsuresPublicly(input: GetBranchKeyIdInput , output: Result<GetBranchKeyIdOutput, Error>)
 // The public method to be called by library consumers
 method GetBranchKeyId ( input: GetBranchKeyIdInput )
 returns (output: Result<GetBranchKeyIdOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetBranchKeyId
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetBranchKeyIdEnsuresPublicly(input, output)
 ensures History.GetBranchKeyId == old(History.GetBranchKeyId) + [DafnyCallEvent(input, output)]
 {
 output := GetBranchKeyId' (input);
 History.GetBranchKeyId := History.GetBranchKeyId + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method GetBranchKeyId' ( input: GetBranchKeyIdInput )
 returns (output: Result<GetBranchKeyIdOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetBranchKeyIdEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 class IClientSupplierCallHistory {
 ghost constructor() {
 GetClient := [];
}
 ghost var GetClient: seq<DafnyCallEvent<GetClientInput, Result<ComAmazonawsKmsTypes.IKeyManagementServiceClient, Error>>>
}
 trait {:termination false} IClientSupplier
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IClientSupplierCallHistory
 predicate GetClientEnsuresPublicly(input: GetClientInput , output: Result<ComAmazonawsKmsTypes.IKeyManagementServiceClient, Error>)
 // The public method to be called by library consumers
 method GetClient ( input: GetClientInput )
 returns (output: Result<ComAmazonawsKmsTypes.IKeyManagementServiceClient, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetClient
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures GetClientEnsuresPublicly(input, output)
 ensures History.GetClient == old(History.GetClient) + [DafnyCallEvent(input, output)]
 {
 output := GetClient' (input);
 History.GetClient := History.GetClient + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method GetClient' ( input: GetClientInput )
 returns (output: Result<ComAmazonawsKmsTypes.IKeyManagementServiceClient, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures GetClientEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 datatype CommitmentPolicy =
 | ESDK(ESDK: ESDKCommitmentPolicy)
 | DBE(DBE: DBECommitmentPolicy)
 datatype CreateAwsKmsDiscoveryKeyringInput = | CreateAwsKmsDiscoveryKeyringInput (
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsDiscoveryMultiKeyringInput = | CreateAwsKmsDiscoveryMultiKeyringInput (
 nameonly regions: RegionList ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsHierarchicalKeyringInput = | CreateAwsKmsHierarchicalKeyringInput (
 nameonly branchKeyId: Option<string> ,
 nameonly branchKeyIdSupplier: Option<IBranchKeyIdSupplier> ,
 nameonly kmsKeyId: KmsKeyId ,
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly ddbClient: ComAmazonawsDynamodbTypes.IDynamoDB_20120810Client ,
 nameonly branchKeyStoreArn: DdbTableArn ,
 nameonly ttlSeconds: PositiveLong ,
 nameonly maxCacheSize: Option<PositiveInteger> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsKeyringInput = | CreateAwsKmsKeyringInput (
 nameonly kmsKeyId: KmsKeyId ,
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkDiscoveryKeyringInput = | CreateAwsKmsMrkDiscoveryKeyringInput (
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly grantTokens: Option<GrantTokenList> ,
 nameonly region: Region
 )
 datatype CreateAwsKmsMrkDiscoveryMultiKeyringInput = | CreateAwsKmsMrkDiscoveryMultiKeyringInput (
 nameonly regions: RegionList ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkKeyringInput = | CreateAwsKmsMrkKeyringInput (
 nameonly kmsKeyId: KmsKeyId ,
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkMultiKeyringInput = | CreateAwsKmsMrkMultiKeyringInput (
 nameonly generator: Option<KmsKeyId> ,
 nameonly kmsKeyIds: Option<KmsKeyIdList> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMultiKeyringInput = | CreateAwsKmsMultiKeyringInput (
 nameonly generator: Option<KmsKeyId> ,
 nameonly kmsKeyIds: Option<KmsKeyIdList> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsRsaKeyringInput = | CreateAwsKmsRsaKeyringInput (
 nameonly publicKey: Option<Secret> ,
 nameonly kmsKeyId: KmsKeyId ,
 nameonly encryptionAlgorithm: ComAmazonawsKmsTypes.EncryptionAlgorithmSpec ,
 nameonly kmsClient: Option<ComAmazonawsKmsTypes.IKeyManagementServiceClient> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateCryptographicMaterialsCacheInput = | CreateCryptographicMaterialsCacheInput (
 nameonly entryCapacity: PositiveInteger ,
 nameonly entryPruningTailSize: Option<PositiveInteger>
 )
 datatype CreateDefaultClientSupplierInput = | CreateDefaultClientSupplierInput (
 
 )
 datatype CreateDefaultCryptographicMaterialsManagerInput = | CreateDefaultCryptographicMaterialsManagerInput (
 nameonly keyring: IKeyring
 )
 datatype CreateExpectedEncryptionContextCMMInput = | CreateExpectedEncryptionContextCMMInput (
 nameonly underlyingCMM: Option<ICryptographicMaterialsManager> ,
 nameonly keyring: Option<IKeyring> ,
 nameonly requiredEncryptionContextKeys: EncryptionContextKeys
 )
 datatype CreateMultiKeyringInput = | CreateMultiKeyringInput (
 nameonly generator: Option<IKeyring> ,
 nameonly childKeyrings: KeyringList
 )
 datatype CreateRawAesKeyringInput = | CreateRawAesKeyringInput (
 nameonly keyNamespace: string ,
 nameonly keyName: string ,
 nameonly wrappingKey: seq<uint8> ,
 nameonly wrappingAlg: AesWrappingAlg
 )
 datatype CreateRawRsaKeyringInput = | CreateRawRsaKeyringInput (
 nameonly keyNamespace: string ,
 nameonly keyName: string ,
 nameonly paddingScheme: PaddingScheme ,
 nameonly publicKey: Option<seq<uint8>> ,
 nameonly privateKey: Option<seq<uint8>>
 )
 class ICryptographicMaterialsCacheCallHistory {
 ghost constructor() {
 PutCacheEntry := [];
 UpdaterUsageMetadata := [];
 GetCacheEntry := [];
 DeleteCacheEntry := [];
}
 ghost var PutCacheEntry: seq<DafnyCallEvent<PutCacheEntryInput, Result<(), Error>>>
 ghost var UpdaterUsageMetadata: seq<DafnyCallEvent<UpdaterUsageMetadataInput, Result<(), Error>>>
 ghost var GetCacheEntry: seq<DafnyCallEvent<GetCacheEntryInput, Result<GetCacheEntryOutput, Error>>>
 ghost var DeleteCacheEntry: seq<DafnyCallEvent<DeleteCacheEntryInput, Result<(), Error>>>
}
 trait {:termination false} ICryptographicMaterialsCache
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // Given that you are mutating state,
// your ValidState function is going to get complicated.

 ghost var Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 // Not only will you need to ensure
// that all your mutable elements are contained in History,
// you MUST also ensure
// that your invariant does not rely on Modifies.
// This means your invariant will begin to look like:
// && History in Modifies
// && this in Modifies                      // so we can read property
// && property in Modifies                  // so we can read properties of property
// && property != History as object        // property really is not History!
// && (forall m <- property.Modifies    // everything in property.Modifies
//    :: m in Modifies - History)              // is in Modifies and really is not History!

 predicate ValidState()
 reads this`Modifies, Modifies - {History}
 ensures ValidState() ==> History in Modifies
  ghost const History: ICryptographicMaterialsCacheCallHistory
 predicate PutCacheEntryEnsuresPublicly(input: PutCacheEntryInput , output: Result<(), Error>)
 // The public method to be called by library consumers
 method PutCacheEntry ( input: PutCacheEntryInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`PutCacheEntry
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures PutCacheEntryEnsuresPublicly(input, output)
 ensures History.PutCacheEntry == old(History.PutCacheEntry) + [DafnyCallEvent(input, output)]
 {
 output := PutCacheEntry' (input);
 History.PutCacheEntry := History.PutCacheEntry + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method PutCacheEntry' ( input: PutCacheEntryInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures PutCacheEntryEnsuresPublicly(input, output)
 ensures unchanged(History)
 
 predicate UpdaterUsageMetadataEnsuresPublicly(input: UpdaterUsageMetadataInput , output: Result<(), Error>)
 // The public method to be called by library consumers
 method UpdaterUsageMetadata ( input: UpdaterUsageMetadataInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UpdaterUsageMetadata
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdaterUsageMetadataEnsuresPublicly(input, output)
 ensures History.UpdaterUsageMetadata == old(History.UpdaterUsageMetadata) + [DafnyCallEvent(input, output)]
 {
 output := UpdaterUsageMetadata' (input);
 History.UpdaterUsageMetadata := History.UpdaterUsageMetadata + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method UpdaterUsageMetadata' ( input: UpdaterUsageMetadataInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UpdaterUsageMetadataEnsuresPublicly(input, output)
 ensures unchanged(History)
 
 predicate GetCacheEntryEnsuresPublicly(input: GetCacheEntryInput , output: Result<GetCacheEntryOutput, Error>)
 // The public method to be called by library consumers
 method GetCacheEntry ( input: GetCacheEntryInput )
 returns (output: Result<GetCacheEntryOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetCacheEntry
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetCacheEntryEnsuresPublicly(input, output)
 ensures History.GetCacheEntry == old(History.GetCacheEntry) + [DafnyCallEvent(input, output)]
 {
 output := GetCacheEntry' (input);
 History.GetCacheEntry := History.GetCacheEntry + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method GetCacheEntry' ( input: GetCacheEntryInput )
 returns (output: Result<GetCacheEntryOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetCacheEntryEnsuresPublicly(input, output)
 ensures unchanged(History)
 
 predicate DeleteCacheEntryEnsuresPublicly(input: DeleteCacheEntryInput , output: Result<(), Error>)
 // The public method to be called by library consumers
 method DeleteCacheEntry ( input: DeleteCacheEntryInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DeleteCacheEntry
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DeleteCacheEntryEnsuresPublicly(input, output)
 ensures History.DeleteCacheEntry == old(History.DeleteCacheEntry) + [DafnyCallEvent(input, output)]
 {
 output := DeleteCacheEntry' (input);
 History.DeleteCacheEntry := History.DeleteCacheEntry + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method DeleteCacheEntry' ( input: DeleteCacheEntryInput )
 returns (output: Result<(), Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DeleteCacheEntryEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 class ICryptographicMaterialsManagerCallHistory {
 ghost constructor() {
 GetEncryptionMaterials := [];
 DecryptMaterials := [];
}
 ghost var GetEncryptionMaterials: seq<DafnyCallEvent<GetEncryptionMaterialsInput, Result<GetEncryptionMaterialsOutput, Error>>>
 ghost var DecryptMaterials: seq<DafnyCallEvent<DecryptMaterialsInput, Result<DecryptMaterialsOutput, Error>>>
}
 trait {:termination false} ICryptographicMaterialsManager
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: ICryptographicMaterialsManagerCallHistory
 predicate GetEncryptionMaterialsEnsuresPublicly(input: GetEncryptionMaterialsInput , output: Result<GetEncryptionMaterialsOutput, Error>)
 // The public method to be called by library consumers
 method GetEncryptionMaterials ( input: GetEncryptionMaterialsInput )
 returns (output: Result<GetEncryptionMaterialsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetEncryptionMaterials
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetEncryptionMaterialsEnsuresPublicly(input, output)
 ensures History.GetEncryptionMaterials == old(History.GetEncryptionMaterials) + [DafnyCallEvent(input, output)]
 {
 output := GetEncryptionMaterials' (input);
 History.GetEncryptionMaterials := History.GetEncryptionMaterials + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method GetEncryptionMaterials' ( input: GetEncryptionMaterialsInput )
 returns (output: Result<GetEncryptionMaterialsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetEncryptionMaterialsEnsuresPublicly(input, output)
 ensures unchanged(History)
 
 predicate DecryptMaterialsEnsuresPublicly(input: DecryptMaterialsInput , output: Result<DecryptMaterialsOutput, Error>)
 // The public method to be called by library consumers
 method DecryptMaterials ( input: DecryptMaterialsInput )
 returns (output: Result<DecryptMaterialsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`DecryptMaterials
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DecryptMaterialsEnsuresPublicly(input, output)
 ensures History.DecryptMaterials == old(History.DecryptMaterials) + [DafnyCallEvent(input, output)]
 {
 output := DecryptMaterials' (input);
 History.DecryptMaterials := History.DecryptMaterials + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method DecryptMaterials' ( input: DecryptMaterialsInput )
 returns (output: Result<DecryptMaterialsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DecryptMaterialsEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 datatype DBEAlgorithmSuiteId =
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384
 datatype DBECommitmentPolicy =
	| REQUIRE_ENCRYPT_REQUIRE_DECRYPT
 type DdbTableArn = string
 datatype DecryptionMaterials = | DecryptionMaterials (
 nameonly algorithmSuite: AlgorithmSuiteInfo ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly requiredEncryptionContextKeys: EncryptionContextKeys ,
 nameonly plaintextDataKey: Option<Secret> ,
 nameonly verificationKey: Option<Secret> ,
 nameonly symmetricSigningKey: Option<Secret>
 )
 datatype DecryptMaterialsInput = | DecryptMaterialsInput (
 nameonly algorithmSuiteId: AlgorithmSuiteId ,
 nameonly commitmentPolicy: CommitmentPolicy ,
 nameonly encryptedDataKeys: EncryptedDataKeyList ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly reproducedEncryptionContext: Option<EncryptionContext>
 )
 datatype DecryptMaterialsOutput = | DecryptMaterialsOutput (
 nameonly decryptionMaterials: DecryptionMaterials
 )
 datatype DeleteCacheEntryInput = | DeleteCacheEntryInput (
 nameonly identifier: seq<uint8>
 )
 datatype DerivationAlgorithm =
 | HKDF(HKDF: HKDF)
 | IDENTITY(IDENTITY: IDENTITY)
 | None(None: None)
 datatype DIRECT_KEY_WRAPPING = | DIRECT_KEY_WRAPPING (
 
 )
 datatype DiscoveryFilter = | DiscoveryFilter (
 nameonly accountIds: AccountIdList ,
 nameonly partition: string
 )
 datatype ECDSA = | ECDSA (
 nameonly curve: AwsCryptographyPrimitivesTypes.ECDSASignatureAlgorithm
 )
 datatype EdkWrappingAlgorithm =
 | DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING: DIRECT_KEY_WRAPPING)
 | IntermediateKeyWrapping(IntermediateKeyWrapping: IntermediateKeyWrapping)
 datatype Encrypt =
 | AES_GCM(AES_GCM: AwsCryptographyPrimitivesTypes.AES_GCM)
 datatype EncryptedDataKey = | EncryptedDataKey (
 nameonly keyProviderId: Utf8Bytes ,
 nameonly keyProviderInfo: seq<uint8> ,
 nameonly ciphertext: seq<uint8>
 )
 type EncryptedDataKeyList = seq<EncryptedDataKey>
 type EncryptionContext = map<Utf8Bytes, Utf8Bytes>
 type EncryptionContextKeys = seq<Utf8Bytes>
 datatype EncryptionMaterials = | EncryptionMaterials (
 nameonly algorithmSuite: AlgorithmSuiteInfo ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly encryptedDataKeys: EncryptedDataKeyList ,
 nameonly requiredEncryptionContextKeys: EncryptionContextKeys ,
 nameonly plaintextDataKey: Option<Secret> ,
 nameonly signingKey: Option<Secret> ,
 nameonly symmetricSigningKeys: Option<SymmetricSigningKeyList>
 )
 datatype ESDKAlgorithmSuiteId =
	| ALG_AES_128_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_192_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_256_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
	| ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
	| ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
 datatype ESDKCommitmentPolicy =
	| FORBID_ENCRYPT_ALLOW_DECRYPT
	| REQUIRE_ENCRYPT_ALLOW_DECRYPT
	| REQUIRE_ENCRYPT_REQUIRE_DECRYPT
 datatype GetBranchKeyIdInput = | GetBranchKeyIdInput (
 nameonly encryptionContext: EncryptionContext
 )
 datatype GetBranchKeyIdOutput = | GetBranchKeyIdOutput (
 nameonly branchKeyId: string
 )
 datatype GetCacheEntryInput = | GetCacheEntryInput (
 nameonly identifier: seq<uint8> ,
 nameonly bytesUsed: Option<int64>
 )
 datatype GetCacheEntryOutput = | GetCacheEntryOutput (
 nameonly materials: Materials ,
 nameonly creationTime: PositiveLong ,
 nameonly expiryTime: PositiveLong ,
 nameonly messagesUsed: PositiveInteger ,
 nameonly bytesUsed: PositiveInteger
 )
 datatype GetClientInput = | GetClientInput (
 nameonly region: Region
 )
 datatype GetEncryptionMaterialsInput = | GetEncryptionMaterialsInput (
 nameonly encryptionContext: EncryptionContext ,
 nameonly commitmentPolicy: CommitmentPolicy ,
 nameonly algorithmSuiteId: Option<AlgorithmSuiteId> ,
 nameonly maxPlaintextLength: Option<int64> ,
 nameonly requiredEncryptionContextKeys: Option<EncryptionContextKeys>
 )
 datatype GetEncryptionMaterialsOutput = | GetEncryptionMaterialsOutput (
 nameonly encryptionMaterials: EncryptionMaterials
 )
 type GrantTokenList = seq<string>
 datatype HierarchicalMaterials = | HierarchicalMaterials (
 nameonly branchKeyVersion: Utf8Bytes ,
 nameonly branchKey: Secret
 )
 datatype HKDF = | HKDF (
 nameonly hmac: AwsCryptographyPrimitivesTypes.DigestAlgorithm ,
 nameonly saltLength: AwsCryptographyPrimitivesTypes.PositiveInteger ,
 nameonly inputKeyLength: AwsCryptographyPrimitivesTypes.SymmetricKeyLength ,
 nameonly outputKeyLength: AwsCryptographyPrimitivesTypes.SymmetricKeyLength
 )
 datatype IDENTITY = | IDENTITY (
 
 )
 datatype InitializeDecryptionMaterialsInput = | InitializeDecryptionMaterialsInput (
 nameonly algorithmSuiteId: AlgorithmSuiteId ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly requiredEncryptionContextKeys: EncryptionContextKeys
 )
 datatype InitializeEncryptionMaterialsInput = | InitializeEncryptionMaterialsInput (
 nameonly algorithmSuiteId: AlgorithmSuiteId ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly requiredEncryptionContextKeys: EncryptionContextKeys ,
 nameonly signingKey: Option<Secret> ,
 nameonly verificationKey: Option<Secret>
 )
 datatype IntermediateKeyWrapping = | IntermediateKeyWrapping (
 nameonly keyEncryptionKeyKdf: DerivationAlgorithm ,
 nameonly macKeyKdf: DerivationAlgorithm ,
 nameonly pdkEncryptAlgorithm: Encrypt
 )
 type KeyringList = seq<IKeyring>
 class IKeyringCallHistory {
 ghost constructor() {
 OnEncrypt := [];
 OnDecrypt := [];
}
 ghost var OnEncrypt: seq<DafnyCallEvent<OnEncryptInput, Result<OnEncryptOutput, Error>>>
 ghost var OnDecrypt: seq<DafnyCallEvent<OnDecryptInput, Result<OnDecryptOutput, Error>>>
}
 trait {:termination false} IKeyring
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IKeyringCallHistory
 predicate OnEncryptEnsuresPublicly(input: OnEncryptInput , output: Result<OnEncryptOutput, Error>)
 // The public method to be called by library consumers
 method OnEncrypt ( input: OnEncryptInput )
 returns (output: Result<OnEncryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`OnEncrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures OnEncryptEnsuresPublicly(input, output)
 ensures History.OnEncrypt == old(History.OnEncrypt) + [DafnyCallEvent(input, output)]
 {
 output := OnEncrypt' (input);
 History.OnEncrypt := History.OnEncrypt + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method OnEncrypt' ( input: OnEncryptInput )
 returns (output: Result<OnEncryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures OnEncryptEnsuresPublicly(input, output)
 ensures unchanged(History)
 
 predicate OnDecryptEnsuresPublicly(input: OnDecryptInput , output: Result<OnDecryptOutput, Error>)
 // The public method to be called by library consumers
 method OnDecrypt ( input: OnDecryptInput )
 returns (output: Result<OnDecryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`OnDecrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures OnDecryptEnsuresPublicly(input, output)
 ensures History.OnDecrypt == old(History.OnDecrypt) + [DafnyCallEvent(input, output)]
 {
 output := OnDecrypt' (input);
 History.OnDecrypt := History.OnDecrypt + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method OnDecrypt' ( input: OnDecryptInput )
 returns (output: Result<OnDecryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures OnDecryptEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 type KmsKeyId = string
 type KmsKeyIdList = seq<KmsKeyId>
 datatype MaterialProvidersConfig = | MaterialProvidersConfig (
 
 )
 datatype Materials =
 | Encryption(Encryption: EncryptionMaterials)
 | Decryption(Decryption: DecryptionMaterials)
 | Hierarchical(Hierarchical: HierarchicalMaterials)
 datatype None = | None (
 
 )
 datatype OnDecryptInput = | OnDecryptInput (
 nameonly materials: DecryptionMaterials ,
 nameonly encryptedDataKeys: EncryptedDataKeyList
 )
 datatype OnDecryptOutput = | OnDecryptOutput (
 nameonly materials: DecryptionMaterials
 )
 datatype OnEncryptInput = | OnEncryptInput (
 nameonly materials: EncryptionMaterials
 )
 datatype OnEncryptOutput = | OnEncryptOutput (
 nameonly materials: EncryptionMaterials
 )
 datatype PaddingScheme =
	| PKCS1
	| OAEP_SHA1_MGF1
	| OAEP_SHA256_MGF1
	| OAEP_SHA384_MGF1
	| OAEP_SHA512_MGF1
 type PositiveInteger = x: int32 | IsValid_PositiveInteger(x) witness *
 predicate method IsValid_PositiveInteger(x: int32) {
 ( 0 <= x  )
}
 type PositiveLong = x: int64 | IsValid_PositiveLong(x) witness *
 predicate method IsValid_PositiveLong(x: int64) {
 ( 0 <= x  )
}
 datatype PutCacheEntryInput = | PutCacheEntryInput (
 nameonly identifier: seq<uint8> ,
 nameonly materials: Materials ,
 nameonly creationTime: PositiveLong ,
 nameonly expiryTime: PositiveLong ,
 nameonly messagesUsed: Option<PositiveInteger> ,
 nameonly bytesUsed: Option<PositiveInteger>
 )
 type Region = string
 type RegionList = seq<Region>
 type Secret = seq<uint8>
 datatype SignatureAlgorithm =
 | ECDSA(ECDSA: ECDSA)
 | None(None: None)
 datatype SymmetricSignatureAlgorithm =
 | HMAC(HMAC: AwsCryptographyPrimitivesTypes.DigestAlgorithm)
 | None(None: None)
 type SymmetricSigningKeyList = seq<Secret>
 datatype UpdaterUsageMetadataInput = | UpdaterUsageMetadataInput (
 nameonly identifier: seq<uint8> ,
 nameonly bytesUsed: PositiveInteger
 )
 type Utf8Bytes = ValidUTF8Bytes
 datatype ValidateCommitmentPolicyOnDecryptInput = | ValidateCommitmentPolicyOnDecryptInput (
 nameonly algorithm: AlgorithmSuiteId ,
 nameonly commitmentPolicy: CommitmentPolicy
 )
 datatype ValidateCommitmentPolicyOnEncryptInput = | ValidateCommitmentPolicyOnEncryptInput (
 nameonly algorithm: AlgorithmSuiteId ,
 nameonly commitmentPolicy: CommitmentPolicy
 )
 datatype ValidDecryptionMaterialsTransitionInput = | ValidDecryptionMaterialsTransitionInput (
 nameonly start: DecryptionMaterials ,
 nameonly stop: DecryptionMaterials
 )
 datatype ValidEncryptionMaterialsTransitionInput = | ValidEncryptionMaterialsTransitionInput (
 nameonly start: EncryptionMaterials ,
 nameonly stop: EncryptionMaterials
 )
 datatype Error =
 // Local Error structures are listed here
 | AwsCryptographicMaterialProvidersException (
 nameonly message: string
 )
 | EntryAlreadyExists (
 nameonly message: string
 )
 | EntryDoesNotExist (
 nameonly message: string
 )
 | InvalidAlgorithmSuiteInfo (
 nameonly message: string
 )
 | InvalidAlgorithmSuiteInfoOnDecrypt (
 nameonly message: string
 )
 | InvalidAlgorithmSuiteInfoOnEncrypt (
 nameonly message: string
 )
 | InvalidDecryptionMaterials (
 nameonly message: string
 )
 | InvalidDecryptionMaterialsTransition (
 nameonly message: string
 )
 | InvalidEncryptionMaterials (
 nameonly message: string
 )
 | InvalidEncryptionMaterialsTransition (
 nameonly message: string
 )
 // Any dependent models are listed here
 | AwsCryptographyPrimitives(AwsCryptographyPrimitives: AwsCryptographyPrimitivesTypes.Error)
 | ComAmazonawsDynamodb(ComAmazonawsDynamodb: ComAmazonawsDynamodbTypes.Error)
 | ComAmazonawsKms(ComAmazonawsKms: ComAmazonawsKmsTypes.Error)
 // The Collection error is used to collect several errors together
 // This is useful when composing OR logic.
 // Consider the following method:
 // 
 // method FN<I, O>(n:I)
 //   returns (res: Result<O, Types.Error>)
 //   ensures A(I).Success? ==> res.Success?
 //   ensures B(I).Success? ==> res.Success?
 //   ensures A(I).Failure? && B(I).Failure? ==> res.Failure?
 // 
 // If either A || B is successful then FN is successful.
 // And if A && B fail then FN will fail.
 // But what information should FN transmit back to the caller?
 // While it may be correct to hide these details from the caller,
 // this can not be the globally correct option.
 // Suppose that A and B can be blocked by different ACLs,
 // and that their representation of I is only eventually consistent.
 // How can the caller distinguish, at a minimum for logging,
 // the difference between the four failure modes?
 // || (!access(A(I)) && !access(B(I)))
 // || (!exit(A(I)) && !exit(B(I)))
 // || (!access(A(I)) && !exit(B(I)))
 // || (!exit(A(I)) && !access(B(I)))
 | CollectionOfErrors(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractAwsCryptographyMaterialProvidersService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyMaterialProvidersTypes
 import Operations : AbstractAwsCryptographyMaterialProvidersOperations
 function method DefaultMaterialProvidersConfig(): MaterialProvidersConfig
 method MaterialProviders(config: MaterialProvidersConfig := DefaultMaterialProvidersConfig())
 returns (res: Result<MaterialProvidersClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()

 class MaterialProvidersClient extends IAwsCryptographicMaterialProvidersClient
 {
 constructor(config: Operations.InternalConfig)
 requires Operations.ValidInternalConfig?(config)
 ensures
 && ValidState()
 && fresh(History)
 && this.config == config
 const config: Operations.InternalConfig
 predicate ValidState()
 ensures ValidState() ==>
 && Operations.ValidInternalConfig?(config)
 && History !in Operations.ModifiesInternalConfig(config)
 && Modifies == Operations.ModifiesInternalConfig(config) + {History}
 predicate CreateAwsKmsKeyringEnsuresPublicly(input: CreateAwsKmsKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsKeyring ( input: CreateAwsKmsKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsKeyring == old(History.CreateAwsKmsKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsKeyring(config, input);
 History.CreateAwsKmsKeyring := History.CreateAwsKmsKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsDiscoveryKeyring ( input: CreateAwsKmsDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsDiscoveryKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsDiscoveryKeyring == old(History.CreateAwsKmsDiscoveryKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsDiscoveryKeyring(config, input);
 History.CreateAwsKmsDiscoveryKeyring := History.CreateAwsKmsDiscoveryKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsMultiKeyringEnsuresPublicly(input: CreateAwsKmsMultiKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsMultiKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsMultiKeyring ( input: CreateAwsKmsMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMultiKeyring == old(History.CreateAwsKmsMultiKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsMultiKeyring(config, input);
 History.CreateAwsKmsMultiKeyring := History.CreateAwsKmsMultiKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsDiscoveryMultiKeyring ( input: CreateAwsKmsDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsDiscoveryMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsDiscoveryMultiKeyring == old(History.CreateAwsKmsDiscoveryMultiKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsDiscoveryMultiKeyring(config, input);
 History.CreateAwsKmsDiscoveryMultiKeyring := History.CreateAwsKmsDiscoveryMultiKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsMrkKeyringEnsuresPublicly(input: CreateAwsKmsMrkKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsMrkKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsMrkKeyring ( input: CreateAwsKmsMrkKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsMrkKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkKeyring == old(History.CreateAwsKmsMrkKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsMrkKeyring(config, input);
 History.CreateAwsKmsMrkKeyring := History.CreateAwsKmsMrkKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkMultiKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsMrkMultiKeyring ( input: CreateAwsKmsMrkMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMrkMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkMultiKeyring == old(History.CreateAwsKmsMrkMultiKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsMrkMultiKeyring(config, input);
 History.CreateAwsKmsMrkMultiKeyring := History.CreateAwsKmsMrkMultiKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsMrkDiscoveryKeyring ( input: CreateAwsKmsMrkDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 modifies Modifies - {History} ,
 input.kmsClient.Modifies ,
 History`CreateAwsKmsMrkDiscoveryKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.kmsClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkDiscoveryKeyring == old(History.CreateAwsKmsMrkDiscoveryKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsMrkDiscoveryKeyring(config, input);
 History.CreateAwsKmsMrkDiscoveryKeyring := History.CreateAwsKmsMrkDiscoveryKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsMrkDiscoveryMultiKeyring ( input: CreateAwsKmsMrkDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 && input.clientSupplier.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ,
 History`CreateAwsKmsMrkDiscoveryMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsMrkDiscoveryMultiKeyring == old(History.CreateAwsKmsMrkDiscoveryMultiKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsMrkDiscoveryMultiKeyring(config, input);
 History.CreateAwsKmsMrkDiscoveryMultiKeyring := History.CreateAwsKmsMrkDiscoveryMultiKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input: CreateAwsKmsHierarchicalKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsHierarchicalKeyring ( input: CreateAwsKmsHierarchicalKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.branchKeyIdSupplier.Some? ==>
 && input.branchKeyIdSupplier.value.ValidState()
 && input.branchKeyIdSupplier.value.Modifies !! {History}
 )
 && input.kmsClient.ValidState()
 && input.kmsClient.Modifies !! {History}
 && input.ddbClient.ValidState()
 && input.ddbClient.Modifies !! {History}
 modifies Modifies - {History} ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies ,
 History`CreateAwsKmsHierarchicalKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) - input.kmsClient.Modifies - input.ddbClient.Modifies ) )
 ensures CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsHierarchicalKeyring == old(History.CreateAwsKmsHierarchicalKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsHierarchicalKeyring(config, input);
 History.CreateAwsKmsHierarchicalKeyring := History.CreateAwsKmsHierarchicalKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateMultiKeyringEnsuresPublicly(input: CreateMultiKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateMultiKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateMultiKeyring ( input: CreateMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.generator.Some? ==>
 && input.generator.value.ValidState()
 && input.generator.value.Modifies !! {History}
 ) && ( forall i <- input.childKeyrings ::
 && i.ValidState()
 && i.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m) ,
 History`CreateMultiKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m)
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.generator.Some? then input.generator.value.Modifies else {}) - (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m) ) )
 ensures CreateMultiKeyringEnsuresPublicly(input, output)
 ensures History.CreateMultiKeyring == old(History.CreateMultiKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateMultiKeyring(config, input);
 History.CreateMultiKeyring := History.CreateMultiKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateRawAesKeyringEnsuresPublicly(input: CreateRawAesKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateRawAesKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateRawAesKeyring ( input: CreateRawAesKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateRawAesKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateRawAesKeyringEnsuresPublicly(input, output)
 ensures History.CreateRawAesKeyring == old(History.CreateRawAesKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateRawAesKeyring(config, input);
 History.CreateRawAesKeyring := History.CreateRawAesKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateRawRsaKeyringEnsuresPublicly(input: CreateRawRsaKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateRawRsaKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateRawRsaKeyring ( input: CreateRawRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateRawRsaKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateRawRsaKeyringEnsuresPublicly(input, output)
 ensures History.CreateRawRsaKeyring == old(History.CreateRawRsaKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateRawRsaKeyring(config, input);
 History.CreateRawRsaKeyring := History.CreateRawRsaKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateAwsKmsRsaKeyringEnsuresPublicly(input: CreateAwsKmsRsaKeyringInput , output: Result<IKeyring, Error>)
 {Operations.CreateAwsKmsRsaKeyringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateAwsKmsRsaKeyring ( input: CreateAwsKmsRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidState() && ( input.kmsClient.Some? ==>
 && input.kmsClient.value.ValidState()
 && input.kmsClient.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {}) ,
 History`CreateAwsKmsRsaKeyring
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {}) ) )
 ensures CreateAwsKmsRsaKeyringEnsuresPublicly(input, output)
 ensures History.CreateAwsKmsRsaKeyring == old(History.CreateAwsKmsRsaKeyring) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateAwsKmsRsaKeyring(config, input);
 History.CreateAwsKmsRsaKeyring := History.CreateAwsKmsRsaKeyring + [DafnyCallEvent(input, output)];
}
 
 predicate CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input: CreateDefaultCryptographicMaterialsManagerInput , output: Result<ICryptographicMaterialsManager, Error>)
 {Operations.CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateDefaultCryptographicMaterialsManager ( input: CreateDefaultCryptographicMaterialsManagerInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidState()
 && input.keyring.ValidState()
 && input.keyring.Modifies !! {History}
 modifies Modifies - {History} ,
 input.keyring.Modifies ,
 History`CreateDefaultCryptographicMaterialsManager
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.keyring.Modifies
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - input.keyring.Modifies ) )
 ensures CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input, output)
 ensures History.CreateDefaultCryptographicMaterialsManager == old(History.CreateDefaultCryptographicMaterialsManager) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateDefaultCryptographicMaterialsManager(config, input);
 History.CreateDefaultCryptographicMaterialsManager := History.CreateDefaultCryptographicMaterialsManager + [DafnyCallEvent(input, output)];
}
 
 predicate CreateExpectedEncryptionContextCMMEnsuresPublicly(input: CreateExpectedEncryptionContextCMMInput , output: Result<ICryptographicMaterialsManager, Error>)
 {Operations.CreateExpectedEncryptionContextCMMEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateExpectedEncryptionContextCMM ( input: CreateExpectedEncryptionContextCMMInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidState() && ( input.underlyingCMM.Some? ==>
 && input.underlyingCMM.value.ValidState()
 && input.underlyingCMM.value.Modifies !! {History}
 ) && ( input.keyring.Some? ==>
 && input.keyring.value.ValidState()
 && input.keyring.value.Modifies !! {History}
 )
 modifies Modifies - {History} ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {}) ,
 History`CreateExpectedEncryptionContextCMM
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {})
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} - (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) - (if input.keyring.Some? then input.keyring.value.Modifies else {}) ) )
 ensures CreateExpectedEncryptionContextCMMEnsuresPublicly(input, output)
 ensures History.CreateExpectedEncryptionContextCMM == old(History.CreateExpectedEncryptionContextCMM) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateExpectedEncryptionContextCMM(config, input);
 History.CreateExpectedEncryptionContextCMM := History.CreateExpectedEncryptionContextCMM + [DafnyCallEvent(input, output)];
}
 
 predicate CreateCryptographicMaterialsCacheEnsuresPublicly(input: CreateCryptographicMaterialsCacheInput , output: Result<ICryptographicMaterialsCache, Error>)
 {Operations.CreateCryptographicMaterialsCacheEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateCryptographicMaterialsCache ( input: CreateCryptographicMaterialsCacheInput )
 returns (output: Result<ICryptographicMaterialsCache, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateCryptographicMaterialsCache
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateCryptographicMaterialsCacheEnsuresPublicly(input, output)
 ensures History.CreateCryptographicMaterialsCache == old(History.CreateCryptographicMaterialsCache) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateCryptographicMaterialsCache(config, input);
 History.CreateCryptographicMaterialsCache := History.CreateCryptographicMaterialsCache + [DafnyCallEvent(input, output)];
}
 
 predicate CreateDefaultClientSupplierEnsuresPublicly(input: CreateDefaultClientSupplierInput , output: Result<IClientSupplier, Error>)
 {Operations.CreateDefaultClientSupplierEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method CreateDefaultClientSupplier ( input: CreateDefaultClientSupplierInput )
 returns (output: Result<IClientSupplier, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`CreateDefaultClientSupplier
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.ValidState()
 && output.value.Modifies !! {History}
 && fresh(output.value)
 && fresh ( output.value.Modifies - Modifies - {History} ) )
 ensures CreateDefaultClientSupplierEnsuresPublicly(input, output)
 ensures History.CreateDefaultClientSupplier == old(History.CreateDefaultClientSupplier) + [DafnyCallEvent(input, output)]
 {
 output := Operations.CreateDefaultClientSupplier(config, input);
 History.CreateDefaultClientSupplier := History.CreateDefaultClientSupplier + [DafnyCallEvent(input, output)];
}
 
 
 // The public method to be called by library consumers
 function method InitializeEncryptionMaterials ( input: InitializeEncryptionMaterialsInput )
 : (output: Result<EncryptionMaterials, Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.InitializeEncryptionMaterials(config, input)
}
 
 
 // The public method to be called by library consumers
 function method InitializeDecryptionMaterials ( input: InitializeDecryptionMaterialsInput )
 : (output: Result<DecryptionMaterials, Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.InitializeDecryptionMaterials(config, input)
}
 
 
 // The public method to be called by library consumers
 function method ValidEncryptionMaterialsTransition ( input: ValidEncryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.ValidEncryptionMaterialsTransition(config, input)
}
 
 
 // The public method to be called by library consumers
 function method ValidDecryptionMaterialsTransition ( input: ValidDecryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.ValidDecryptionMaterialsTransition(config, input)
}
 
 
 // The public method to be called by library consumers
 function method EncryptionMaterialsHasPlaintextDataKey ( input: EncryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.EncryptionMaterialsHasPlaintextDataKey(config, input)
}
 
 
 // The public method to be called by library consumers
 function method DecryptionMaterialsWithPlaintextDataKey ( input: DecryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.DecryptionMaterialsWithPlaintextDataKey(config, input)
}
 
 
 // The public method to be called by library consumers
 function method GetAlgorithmSuiteInfo ( input: seq<uint8> )
 : (output: Result<AlgorithmSuiteInfo, Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.GetAlgorithmSuiteInfo(config, input)
}
 
 
 // The public method to be called by library consumers
 function method ValidAlgorithmSuiteInfo ( input: AlgorithmSuiteInfo )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.ValidAlgorithmSuiteInfo(config, input)
}
 
 
 // The public method to be called by library consumers
 function method ValidateCommitmentPolicyOnEncrypt ( input: ValidateCommitmentPolicyOnEncryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.ValidateCommitmentPolicyOnEncrypt(config, input)
}
 
 
 // The public method to be called by library consumers
 function method ValidateCommitmentPolicyOnDecrypt ( input: ValidateCommitmentPolicyOnDecryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
 {
 Operations.ValidateCommitmentPolicyOnDecrypt(config, input)
}
 
}
}
 abstract module AbstractAwsCryptographyMaterialProvidersOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyMaterialProvidersTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate CreateAwsKmsKeyringEnsuresPublicly(input: CreateAwsKmsKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsKeyring ( config: InternalConfig , input: CreateAwsKmsKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.kmsClient.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsDiscoveryKeyring ( config: InternalConfig , input: CreateAwsKmsDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.kmsClient.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsDiscoveryKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsMultiKeyringEnsuresPublicly(input: CreateAwsKmsMultiKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsMultiKeyring ( config: InternalConfig , input: CreateAwsKmsMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMultiKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsDiscoveryMultiKeyring ( config: InternalConfig , input: CreateAwsKmsDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsDiscoveryMultiKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsMrkKeyringEnsuresPublicly(input: CreateAwsKmsMrkKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsMrkKeyring ( config: InternalConfig , input: CreateAwsKmsMrkKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.kmsClient.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkMultiKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsMrkMultiKeyring ( config: InternalConfig , input: CreateAwsKmsMrkMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkMultiKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsMrkDiscoveryKeyring ( config: InternalConfig , input: CreateAwsKmsMrkDiscoveryKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.kmsClient.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.kmsClient.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - input.kmsClient.Modifies ) )
 ensures CreateAwsKmsMrkDiscoveryKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input: CreateAwsKmsMrkDiscoveryMultiKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsMrkDiscoveryMultiKeyring ( config: InternalConfig , input: CreateAwsKmsMrkDiscoveryMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.clientSupplier.Some? ==>
 && input.clientSupplier.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.clientSupplier.Some? then input.clientSupplier.value.Modifies else {}) ) )
 ensures CreateAwsKmsMrkDiscoveryMultiKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input: CreateAwsKmsHierarchicalKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsHierarchicalKeyring ( config: InternalConfig , input: CreateAwsKmsHierarchicalKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.branchKeyIdSupplier.Some? ==>
 && input.branchKeyIdSupplier.value.ValidState()
 )
 && input.kmsClient.ValidState()
 && input.ddbClient.ValidState()
 modifies ModifiesInternalConfig(config) ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) ,
 input.kmsClient.Modifies ,
 input.ddbClient.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.branchKeyIdSupplier.Some? then input.branchKeyIdSupplier.value.Modifies else {}) - input.kmsClient.Modifies - input.ddbClient.Modifies ) )
 ensures CreateAwsKmsHierarchicalKeyringEnsuresPublicly(input, output)


 predicate CreateMultiKeyringEnsuresPublicly(input: CreateMultiKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateMultiKeyring ( config: InternalConfig , input: CreateMultiKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.generator.Some? ==>
 && input.generator.value.ValidState()
 ) && ( forall i <- input.childKeyrings ::
 && i.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.generator.Some? then input.generator.value.Modifies else {}) ,
 (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.generator.Some? then input.generator.value.Modifies else {}) - (set m: object, i | i in input.childKeyrings && m in i.Modifies :: m) ) )
 ensures CreateMultiKeyringEnsuresPublicly(input, output)


 predicate CreateRawAesKeyringEnsuresPublicly(input: CreateRawAesKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateRawAesKeyring ( config: InternalConfig , input: CreateRawAesKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) ) )
 ensures CreateRawAesKeyringEnsuresPublicly(input, output)


 predicate CreateRawRsaKeyringEnsuresPublicly(input: CreateRawRsaKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateRawRsaKeyring ( config: InternalConfig , input: CreateRawRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) ) )
 ensures CreateRawRsaKeyringEnsuresPublicly(input, output)


 predicate CreateAwsKmsRsaKeyringEnsuresPublicly(input: CreateAwsKmsRsaKeyringInput , output: Result<IKeyring, Error>)
 // The private method to be refined by the library developer


 method CreateAwsKmsRsaKeyring ( config: InternalConfig , input: CreateAwsKmsRsaKeyringInput )
 returns (output: Result<IKeyring, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.kmsClient.Some? ==>
 && input.kmsClient.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.kmsClient.Some? then input.kmsClient.value.Modifies else {}) ) )
 ensures CreateAwsKmsRsaKeyringEnsuresPublicly(input, output)


 predicate CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input: CreateDefaultCryptographicMaterialsManagerInput , output: Result<ICryptographicMaterialsManager, Error>)
 // The private method to be refined by the library developer


 method CreateDefaultCryptographicMaterialsManager ( config: InternalConfig , input: CreateDefaultCryptographicMaterialsManagerInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.keyring.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.keyring.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.keyring.Modifies
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - input.keyring.Modifies ) )
 ensures CreateDefaultCryptographicMaterialsManagerEnsuresPublicly(input, output)


 predicate CreateExpectedEncryptionContextCMMEnsuresPublicly(input: CreateExpectedEncryptionContextCMMInput , output: Result<ICryptographicMaterialsManager, Error>)
 // The private method to be refined by the library developer


 method CreateExpectedEncryptionContextCMM ( config: InternalConfig , input: CreateExpectedEncryptionContextCMMInput )
 returns (output: Result<ICryptographicMaterialsManager, Error>)
 requires
 && ValidInternalConfig?(config) && ( input.underlyingCMM.Some? ==>
 && input.underlyingCMM.value.ValidState()
 ) && ( input.keyring.Some? ==>
 && input.keyring.value.ValidState()
 )
 modifies ModifiesInternalConfig(config) ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {})
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) ,
 (if input.keyring.Some? then input.keyring.value.Modifies else {})
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) - (if input.underlyingCMM.Some? then input.underlyingCMM.value.Modifies else {}) - (if input.keyring.Some? then input.keyring.value.Modifies else {}) ) )
 ensures CreateExpectedEncryptionContextCMMEnsuresPublicly(input, output)


 predicate CreateCryptographicMaterialsCacheEnsuresPublicly(input: CreateCryptographicMaterialsCacheInput , output: Result<ICryptographicMaterialsCache, Error>)
 // The private method to be refined by the library developer


 method CreateCryptographicMaterialsCache ( config: InternalConfig , input: CreateCryptographicMaterialsCacheInput )
 returns (output: Result<ICryptographicMaterialsCache, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) ) )
 ensures CreateCryptographicMaterialsCacheEnsuresPublicly(input, output)


 predicate CreateDefaultClientSupplierEnsuresPublicly(input: CreateDefaultClientSupplierInput , output: Result<IClientSupplier, Error>)
 // The private method to be refined by the library developer


 method CreateDefaultClientSupplier ( config: InternalConfig , input: CreateDefaultClientSupplierInput )
 returns (output: Result<IClientSupplier, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.ValidState()
 && fresh(output.value)
 && fresh ( output.value.Modifies - ModifiesInternalConfig(config) ) )
 ensures CreateDefaultClientSupplierEnsuresPublicly(input, output)


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method InitializeEncryptionMaterials ( config: InternalConfig , input: InitializeEncryptionMaterialsInput )
 : (output: Result<EncryptionMaterials, Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method InitializeDecryptionMaterials ( config: InternalConfig , input: InitializeDecryptionMaterialsInput )
 : (output: Result<DecryptionMaterials, Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method ValidEncryptionMaterialsTransition ( config: InternalConfig , input: ValidEncryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method ValidDecryptionMaterialsTransition ( config: InternalConfig , input: ValidDecryptionMaterialsTransitionInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method EncryptionMaterialsHasPlaintextDataKey ( config: InternalConfig , input: EncryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method DecryptionMaterialsWithPlaintextDataKey ( config: InternalConfig , input: DecryptionMaterials )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method GetAlgorithmSuiteInfo ( config: InternalConfig , input: seq<uint8> )
 : (output: Result<AlgorithmSuiteInfo, Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method ValidAlgorithmSuiteInfo ( config: InternalConfig , input: AlgorithmSuiteInfo )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method ValidateCommitmentPolicyOnEncrypt ( config: InternalConfig , input: ValidateCommitmentPolicyOnEncryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures


 // Functions are deterministic, no need for historical call events or ensures indirection
 // The private method to be refined by the library developer


 function method ValidateCommitmentPolicyOnDecrypt ( config: InternalConfig , input: ValidateCommitmentPolicyOnDecryptInput )
 : (output: Result<(), Error>)
 // Functions that are transparent do not need ensures
}
