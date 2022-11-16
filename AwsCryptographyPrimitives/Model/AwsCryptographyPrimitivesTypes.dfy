// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/src/Index.dfy"
 module {:extern "Dafny.Aws.Cryptography.Primitives.Types" } AwsCryptographyPrimitivesTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 datatype AES_GCM = | AES_GCM (
 nameonly keyLength: SymmetricKeyLength ,
 nameonly tagLength: Uint8Bytes ,
 nameonly ivLength: Uint8Bits
 )
 datatype AESDecryptInput = | AESDecryptInput (
 nameonly encAlg: AES_GCM ,
 nameonly key: seq<uint8> ,
 nameonly cipherTxt: seq<uint8> ,
 nameonly authTag: seq<uint8> ,
 nameonly iv: seq<uint8> ,
 nameonly aad: seq<uint8>
 )
 datatype AESEncryptInput = | AESEncryptInput (
 nameonly encAlg: AES_GCM ,
 nameonly iv: seq<uint8> ,
 nameonly key: seq<uint8> ,
 nameonly msg: seq<uint8> ,
 nameonly aad: seq<uint8>
 )
 datatype AESEncryptOutput = | AESEncryptOutput (
 nameonly cipherText: seq<uint8> ,
 nameonly authTag: seq<uint8>
 )
 class IAwsCryptographicPrimitivesClientCallHistory {
 ghost constructor() {
 GenerateRandomBytes := [];
 Digest := [];
 HMac := [];
 HkdfExtract := [];
 HkdfExpand := [];
 Hkdf := [];
 AESEncrypt := [];
 AESDecrypt := [];
 GenerateRSAKeyPair := [];
 RSADecrypt := [];
 RSAEncrypt := [];
 GenerateECDSASignatureKey := [];
 ECDSASign := [];
 ECDSAVerify := [];
}
 ghost var GenerateRandomBytes: seq<DafnyCallEvent<GenerateRandomBytesInput, Result<seq<uint8>, Error>>>
 ghost var Digest: seq<DafnyCallEvent<DigestInput, Result<seq<uint8>, Error>>>
 ghost var HMac: seq<DafnyCallEvent<HMacInput, Result<seq<uint8>, Error>>>
 ghost var HkdfExtract: seq<DafnyCallEvent<HkdfExtractInput, Result<seq<uint8>, Error>>>
 ghost var HkdfExpand: seq<DafnyCallEvent<HkdfExpandInput, Result<seq<uint8>, Error>>>
 ghost var Hkdf: seq<DafnyCallEvent<HkdfInput, Result<seq<uint8>, Error>>>
 ghost var AESEncrypt: seq<DafnyCallEvent<AESEncryptInput, Result<AESEncryptOutput, Error>>>
 ghost var AESDecrypt: seq<DafnyCallEvent<AESDecryptInput, Result<seq<uint8>, Error>>>
 ghost var GenerateRSAKeyPair: seq<DafnyCallEvent<GenerateRSAKeyPairInput, Result<GenerateRSAKeyPairOutput, Error>>>
 ghost var RSADecrypt: seq<DafnyCallEvent<RSADecryptInput, Result<seq<uint8>, Error>>>
 ghost var RSAEncrypt: seq<DafnyCallEvent<RSAEncryptInput, Result<seq<uint8>, Error>>>
 ghost var GenerateECDSASignatureKey: seq<DafnyCallEvent<GenerateECDSASignatureKeyInput, Result<GenerateECDSASignatureKeyOutput, Error>>>
 ghost var ECDSASign: seq<DafnyCallEvent<ECDSASignInput, Result<seq<uint8>, Error>>>
 ghost var ECDSAVerify: seq<DafnyCallEvent<ECDSAVerifyInput, Result<bool, Error>>>
}
 trait {:termination false} IAwsCryptographicPrimitivesClient
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
 // Modifies := {History};
 ghost const Modifies: set<object>
 // For an unassigned const field defined in a trait,
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
 // Then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 ensures ValidState() ==> History in Modifies
  ghost const History: IAwsCryptographicPrimitivesClientCallHistory
 predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method GenerateRandomBytes ( input: GenerateRandomBytesInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateRandomBytes
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateRandomBytesEnsuresPublicly(input, output)
 ensures History.GenerateRandomBytes == old(History.GenerateRandomBytes) + [DafnyCallEvent(input, output)]
 
 predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method Digest ( input: DigestInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Digest
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DigestEnsuresPublicly(input, output)
 ensures History.Digest == old(History.Digest) + [DafnyCallEvent(input, output)]
 
 predicate HMacEnsuresPublicly(input: HMacInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method HMac ( input: HMacInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HMac
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HMacEnsuresPublicly(input, output)
 ensures History.HMac == old(History.HMac) + [DafnyCallEvent(input, output)]
 
 predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method HkdfExtract ( input: HkdfExtractInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HkdfExtract
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfExtractEnsuresPublicly(input, output)
 ensures History.HkdfExtract == old(History.HkdfExtract) + [DafnyCallEvent(input, output)]
 
 predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method HkdfExpand ( input: HkdfExpandInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HkdfExpand
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfExpandEnsuresPublicly(input, output)
 ensures History.HkdfExpand == old(History.HkdfExpand) + [DafnyCallEvent(input, output)]
 
 predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method Hkdf ( input: HkdfInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Hkdf
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfEnsuresPublicly(input, output)
 ensures History.Hkdf == old(History.Hkdf) + [DafnyCallEvent(input, output)]
 
 predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
 // The public method to be called by library consumers
 method AESEncrypt ( input: AESEncryptInput )
 returns (output: Result<AESEncryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`AESEncrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures AESEncryptEnsuresPublicly(input, output)
 ensures History.AESEncrypt == old(History.AESEncrypt) + [DafnyCallEvent(input, output)]
 
 predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method AESDecrypt ( input: AESDecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`AESDecrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures AESDecryptEnsuresPublicly(input, output)
 ensures History.AESDecrypt == old(History.AESDecrypt) + [DafnyCallEvent(input, output)]
 
 predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
 // The public method to be called by library consumers
 method GenerateRSAKeyPair ( input: GenerateRSAKeyPairInput )
 returns (output: Result<GenerateRSAKeyPairOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateRSAKeyPair
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
 ensures History.GenerateRSAKeyPair == old(History.GenerateRSAKeyPair) + [DafnyCallEvent(input, output)]
 
 predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method RSADecrypt ( input: RSADecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RSADecrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RSADecryptEnsuresPublicly(input, output)
 ensures History.RSADecrypt == old(History.RSADecrypt) + [DafnyCallEvent(input, output)]
 
 predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method RSAEncrypt ( input: RSAEncryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RSAEncrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RSAEncryptEnsuresPublicly(input, output)
 ensures History.RSAEncrypt == old(History.RSAEncrypt) + [DafnyCallEvent(input, output)]
 
 predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
 // The public method to be called by library consumers
 method GenerateECDSASignatureKey ( input: GenerateECDSASignatureKeyInput )
 returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateECDSASignatureKey
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
 ensures History.GenerateECDSASignatureKey == old(History.GenerateECDSASignatureKey) + [DafnyCallEvent(input, output)]
 
 predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
 // The public method to be called by library consumers
 method ECDSASign ( input: ECDSASignInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ECDSASign
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ECDSASignEnsuresPublicly(input, output)
 ensures History.ECDSASign == old(History.ECDSASign) + [DafnyCallEvent(input, output)]
 
 predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
 // The public method to be called by library consumers
 method ECDSAVerify ( input: ECDSAVerifyInput )
 returns (output: Result<bool, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ECDSAVerify
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ECDSAVerifyEnsuresPublicly(input, output)
 ensures History.ECDSAVerify == old(History.ECDSAVerify) + [DafnyCallEvent(input, output)]
 
}
 datatype CryptoConfig = | CryptoConfig (
 
 )
 datatype DigestAlgorithm =
	| SHA_512
	| SHA_384
	| SHA_256
	| SHA_1
 datatype DigestInput = | DigestInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly message: seq<uint8>
 )
 datatype ECDSASignatureAlgorithm =
	| ECDSA_P384
	| ECDSA_P256
 datatype ECDSASignInput = | ECDSASignInput (
 nameonly signatureAlgorithm: ECDSASignatureAlgorithm ,
 nameonly signingKey: seq<uint8> ,
 nameonly message: seq<uint8>
 )
 datatype ECDSAVerifyInput = | ECDSAVerifyInput (
 nameonly signatureAlgorithm: ECDSASignatureAlgorithm ,
 nameonly verificationKey: seq<uint8> ,
 nameonly message: seq<uint8> ,
 nameonly signature: seq<uint8>
 )
 datatype GenerateECDSASignatureKeyInput = | GenerateECDSASignatureKeyInput (
 nameonly signatureAlgorithm: ECDSASignatureAlgorithm
 )
 datatype GenerateECDSASignatureKeyOutput = | GenerateECDSASignatureKeyOutput (
 nameonly signatureAlgorithm: ECDSASignatureAlgorithm ,
 nameonly verificationKey: seq<uint8> ,
 nameonly signingKey: seq<uint8>
 )
 datatype GenerateRandomBytesInput = | GenerateRandomBytesInput (
 nameonly length: PositiveInteger
 )
 datatype GenerateRSAKeyPairInput = | GenerateRSAKeyPairInput (
 nameonly strength: RSAStrengthBits
 )
 datatype GenerateRSAKeyPairOutput = | GenerateRSAKeyPairOutput (
 nameonly publicKey: RSAPublicKey ,
 nameonly privateKey: RSAPrivateKey
 )
 datatype HkdfExpandInput = | HkdfExpandInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly prk: seq<uint8> ,
 nameonly info: seq<uint8> ,
 nameonly expectedLength: PositiveInteger
 )
 datatype HkdfExtractInput = | HkdfExtractInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8>
 )
 datatype HkdfInput = | HkdfInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8> ,
 nameonly info: seq<uint8> ,
 nameonly expectedLength: PositiveInteger
 )
 datatype HMacInput = | HMacInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly key: seq<uint8> ,
 nameonly message: seq<uint8>
 )
 type PositiveInteger = x: int32 | IsValid_PositiveInteger(x) witness *
 predicate method IsValid_PositiveInteger(x: int32) {
 ( 0 <= x  )
}
 datatype RSADecryptInput = | RSADecryptInput (
 nameonly padding: RSAPaddingMode ,
 nameonly privateKey: seq<uint8> ,
 nameonly cipherText: seq<uint8>
 )
 datatype RSAEncryptInput = | RSAEncryptInput (
 nameonly padding: RSAPaddingMode ,
 nameonly publicKey: seq<uint8> ,
 nameonly plaintext: seq<uint8>
 )
 datatype RSAPaddingMode =
	| PKCS1
	| OAEP_SHA1
	| OAEP_SHA256
	| OAEP_SHA384
	| OAEP_SHA512
 datatype RSAPrivateKey = | RSAPrivateKey (
 nameonly strength: RSAStrengthBits ,
 nameonly pem: seq<uint8>
 )
 datatype RSAPublicKey = | RSAPublicKey (
 nameonly strength: RSAStrengthBits ,
 nameonly pem: seq<uint8>
 )
 type RSAStrengthBits = x: int32 | IsValid_RSAStrengthBits(x) witness *
 predicate method IsValid_RSAStrengthBits(x: int32) {
 ( 81 <= x <= 4096 )
}
 type SymmetricKeyLength = x: int32 | IsValid_SymmetricKeyLength(x) witness *
 predicate method IsValid_SymmetricKeyLength(x: int32) {
 ( 1 <= x <= 32 )
}
 type Uint8Bits = x: int32 | IsValid_Uint8Bits(x) witness *
 predicate method IsValid_Uint8Bits(x: int32) {
 ( 0 <= x <= 255 )
}
 type Uint8Bytes = x: int32 | IsValid_Uint8Bytes(x) witness *
 predicate method IsValid_Uint8Bytes(x: int32) {
 ( 0 <= x <= 32 )
}
 datatype Error =
 // Local Error structures are listed here
 | AwsCryptographicPrimitivesError (
 nameonly message: string
 )
 // Any dependent models are listed here
 
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
 | Collection(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractAwsCryptographyPrimitivesService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyPrimitivesTypes
 import Operations : AbstractAwsCryptographyPrimitivesOperations
 function method DefaultCryptoConfig(): CryptoConfig
 method AtomicPrimitives(config: CryptoConfig := DefaultCryptoConfig())
 returns (res: Result<AtomicPrimitivesClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
 class AtomicPrimitivesClient extends IAwsCryptographicPrimitivesClient
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
 predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
 {Operations.GenerateRandomBytesEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GenerateRandomBytes ( input: GenerateRandomBytesInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateRandomBytes
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateRandomBytesEnsuresPublicly(input, output)
 ensures History.GenerateRandomBytes == old(History.GenerateRandomBytes) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GenerateRandomBytes(config, input);
 History.GenerateRandomBytes := History.GenerateRandomBytes + [DafnyCallEvent(input, output)];
}
 
 predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
 {Operations.DigestEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method Digest ( input: DigestInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Digest
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures DigestEnsuresPublicly(input, output)
 ensures History.Digest == old(History.Digest) + [DafnyCallEvent(input, output)]
 {
 output := Operations.Digest(config, input);
 History.Digest := History.Digest + [DafnyCallEvent(input, output)];
}
 
 predicate HMacEnsuresPublicly(input: HMacInput, output: Result<seq<uint8>, Error>)
 {Operations.HMacEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method HMac ( input: HMacInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HMac
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HMacEnsuresPublicly(input, output)
 ensures History.HMac == old(History.HMac) + [DafnyCallEvent(input, output)]
 {
 output := Operations.HMac(config, input);
 History.HMac := History.HMac + [DafnyCallEvent(input, output)];
}
 
 predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
 {Operations.HkdfExtractEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method HkdfExtract ( input: HkdfExtractInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HkdfExtract
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfExtractEnsuresPublicly(input, output)
 ensures History.HkdfExtract == old(History.HkdfExtract) + [DafnyCallEvent(input, output)]
 {
 output := Operations.HkdfExtract(config, input);
 History.HkdfExtract := History.HkdfExtract + [DafnyCallEvent(input, output)];
}
 
 predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
 {Operations.HkdfExpandEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method HkdfExpand ( input: HkdfExpandInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`HkdfExpand
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfExpandEnsuresPublicly(input, output)
 ensures History.HkdfExpand == old(History.HkdfExpand) + [DafnyCallEvent(input, output)]
 {
 output := Operations.HkdfExpand(config, input);
 History.HkdfExpand := History.HkdfExpand + [DafnyCallEvent(input, output)];
}
 
 predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
 {Operations.HkdfEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method Hkdf ( input: HkdfInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`Hkdf
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures HkdfEnsuresPublicly(input, output)
 ensures History.Hkdf == old(History.Hkdf) + [DafnyCallEvent(input, output)]
 {
 output := Operations.Hkdf(config, input);
 History.Hkdf := History.Hkdf + [DafnyCallEvent(input, output)];
}
 
 predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
 {Operations.AESEncryptEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method AESEncrypt ( input: AESEncryptInput )
 returns (output: Result<AESEncryptOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`AESEncrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures AESEncryptEnsuresPublicly(input, output)
 ensures History.AESEncrypt == old(History.AESEncrypt) + [DafnyCallEvent(input, output)]
 {
 output := Operations.AESEncrypt(config, input);
 History.AESEncrypt := History.AESEncrypt + [DafnyCallEvent(input, output)];
}
 
 predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
 {Operations.AESDecryptEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method AESDecrypt ( input: AESDecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`AESDecrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures AESDecryptEnsuresPublicly(input, output)
 ensures History.AESDecrypt == old(History.AESDecrypt) + [DafnyCallEvent(input, output)]
 {
 output := Operations.AESDecrypt(config, input);
 History.AESDecrypt := History.AESDecrypt + [DafnyCallEvent(input, output)];
}
 
 predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
 {Operations.GenerateRSAKeyPairEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GenerateRSAKeyPair ( input: GenerateRSAKeyPairInput )
 returns (output: Result<GenerateRSAKeyPairOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateRSAKeyPair
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
 ensures History.GenerateRSAKeyPair == old(History.GenerateRSAKeyPair) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GenerateRSAKeyPair(config, input);
 History.GenerateRSAKeyPair := History.GenerateRSAKeyPair + [DafnyCallEvent(input, output)];
}
 
 predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
 {Operations.RSADecryptEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method RSADecrypt ( input: RSADecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RSADecrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RSADecryptEnsuresPublicly(input, output)
 ensures History.RSADecrypt == old(History.RSADecrypt) + [DafnyCallEvent(input, output)]
 {
 output := Operations.RSADecrypt(config, input);
 History.RSADecrypt := History.RSADecrypt + [DafnyCallEvent(input, output)];
}
 
 predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
 {Operations.RSAEncryptEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method RSAEncrypt ( input: RSAEncryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`RSAEncrypt
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures RSAEncryptEnsuresPublicly(input, output)
 ensures History.RSAEncrypt == old(History.RSAEncrypt) + [DafnyCallEvent(input, output)]
 {
 output := Operations.RSAEncrypt(config, input);
 History.RSAEncrypt := History.RSAEncrypt + [DafnyCallEvent(input, output)];
}
 
 predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
 {Operations.GenerateECDSASignatureKeyEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GenerateECDSASignatureKey ( input: GenerateECDSASignatureKeyInput )
 returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GenerateECDSASignatureKey
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
 ensures History.GenerateECDSASignatureKey == old(History.GenerateECDSASignatureKey) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GenerateECDSASignatureKey(config, input);
 History.GenerateECDSASignatureKey := History.GenerateECDSASignatureKey + [DafnyCallEvent(input, output)];
}
 
 predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
 {Operations.ECDSASignEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method ECDSASign ( input: ECDSASignInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ECDSASign
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ECDSASignEnsuresPublicly(input, output)
 ensures History.ECDSASign == old(History.ECDSASign) + [DafnyCallEvent(input, output)]
 {
 output := Operations.ECDSASign(config, input);
 History.ECDSASign := History.ECDSASign + [DafnyCallEvent(input, output)];
}
 
 predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
 {Operations.ECDSAVerifyEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method ECDSAVerify ( input: ECDSAVerifyInput )
 returns (output: Result<bool, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`ECDSAVerify
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures ECDSAVerifyEnsuresPublicly(input, output)
 ensures History.ECDSAVerify == old(History.ECDSAVerify) + [DafnyCallEvent(input, output)]
 {
 output := Operations.ECDSAVerify(config, input);
 History.ECDSAVerify := History.ECDSAVerify + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractAwsCryptographyPrimitivesOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyPrimitivesTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method GenerateRandomBytes ( config: InternalConfig,  input: GenerateRandomBytesInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GenerateRandomBytesEnsuresPublicly(input, output)


 predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method Digest ( config: InternalConfig,  input: DigestInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures DigestEnsuresPublicly(input, output)


 predicate HMacEnsuresPublicly(input: HMacInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method HMac ( config: InternalConfig,  input: HMacInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures HMacEnsuresPublicly(input, output)


 predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method HkdfExtract ( config: InternalConfig,  input: HkdfExtractInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures HkdfExtractEnsuresPublicly(input, output)


 predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method HkdfExpand ( config: InternalConfig,  input: HkdfExpandInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures HkdfExpandEnsuresPublicly(input, output)


 predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method Hkdf ( config: InternalConfig,  input: HkdfInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures HkdfEnsuresPublicly(input, output)


 predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
 // The private method to be refined by the library developer


 method AESEncrypt ( config: InternalConfig,  input: AESEncryptInput )
 returns (output: Result<AESEncryptOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures AESEncryptEnsuresPublicly(input, output)


 predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method AESDecrypt ( config: InternalConfig,  input: AESDecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures AESDecryptEnsuresPublicly(input, output)


 predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
 // The private method to be refined by the library developer


 method GenerateRSAKeyPair ( config: InternalConfig,  input: GenerateRSAKeyPairInput )
 returns (output: Result<GenerateRSAKeyPairOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GenerateRSAKeyPairEnsuresPublicly(input, output)


 predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method RSADecrypt ( config: InternalConfig,  input: RSADecryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures RSADecryptEnsuresPublicly(input, output)


 predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method RSAEncrypt ( config: InternalConfig,  input: RSAEncryptInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures RSAEncryptEnsuresPublicly(input, output)


 predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
 // The private method to be refined by the library developer


 method GenerateECDSASignatureKey ( config: InternalConfig,  input: GenerateECDSASignatureKeyInput )
 returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)


 predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
 // The private method to be refined by the library developer


 method ECDSASign ( config: InternalConfig,  input: ECDSASignInput )
 returns (output: Result<seq<uint8>, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ECDSASignEnsuresPublicly(input, output)


 predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
 // The private method to be refined by the library developer


 method ECDSAVerify ( config: InternalConfig,  input: ECDSAVerifyInput )
 returns (output: Result<bool, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures ECDSAVerifyEnsuresPublicly(input, output)
}
