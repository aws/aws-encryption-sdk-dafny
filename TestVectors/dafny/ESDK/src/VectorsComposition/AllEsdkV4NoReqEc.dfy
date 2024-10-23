// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"

module {:options "/functionSyntax:4" } AllEsdkV4NoReqEc {
  import Types = AwsCryptographyEncryptionSdkTypes
  import mplTypes = AwsCryptographyMaterialProvidersTypes
  import keyVectorKeyTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import EncryptionSdk
  import MaterialProviders
  import opened CompleteVectors
  import opened KeyDescription
  import opened Wrappers
  import opened StandardLibrary.UInt
  import HexStrings
  import opened JSON.Values
  import JSONHelpers
  import EsdkManifestOptions
  import EsdkTestVectors
  
  import AllHierarchy
  import AllKms
  import AllKmsMrkAware
  import AllKmsMrkAwareDiscovery
  import AllKmsRsa
  import AllKmsEcdh
  import AllRawAES
  import AllRawRSA
  import AllRawECDH
  import AllDefaultCmm
  import AllRequiredEncryptionContextCmm
  import AllMulti

  import UUID
  import UTF8
  import JSON.API
  import SortedSets
  import FileIO
  
  // This is a HACK!
  // This is *ONLY* because this is wrapping the MPL
  import AlgorithmSuites
  
  const frameSize: int64 := 512

  const AllPositiveKeyDescriptions
  := {}
      + AllHierarchy.KeyDescriptions
      + AllKms.KeyDescriptions
      + AllKmsMrkAware.KeyDescriptions
      + AllKmsMrkAwareDiscovery.KeyDescriptions
      + AllKmsRsa.KeyDescriptions
      + AllRawAES.KeyDescriptions
      + AllRawRSA.KeyDescriptions
      + AllMulti.KeyDescriptions

  function keyDescriptionToName(keyDescription: keyVectorKeyTypes.KeyDescription): (output: string)
  {
    match keyDescription
      case Kms => "KMS"
      case KmsMrk => "KMS-MRK"
      case KmsMrkDiscovery => "KMS-MRK-Discovery"
      case RSA => "Raw RSA"
      case AES => "Raw AES"
      case ECDH => "Raw ECDH"
      case Static => "Static Keyring"
      case KmsRsa => "KMS RSA"
      case KmsECDH => "KMS ECDH"
      case Hierarchy => "Hierarchy"
      case Multi => "MultiKeyring"
      case RequiredEncryptionContext => "RequiredEncryptionContext"
  }

  // All these tests will use a defualt CMM no ECDH
  const AllPostiveKeyringTestsNoDBESuiteNoReqECNoEcdh :=
  set
    postiveKeyDescription <- AllPositiveKeyDescriptions,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(postiveKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 4,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [postiveKeyDescription],
        decryptDescriptions := [postiveKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )
  
  // All these tests will use a defualt CMM only Raw ECDH
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithEphemeralRawEcdh :=
  set
    encryptKeyDescription <- AllRawECDH.EphemeralKeyDescriptionsEncrypt,
    decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticRawEcdh :=
  set
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.RecipientKeyDescriptions | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticDiscoveryRawEcdh :=
  set
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )
  
  // All these tests will use a defualt CMM only Kms ECDH
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticKmsEcdh :=
  set
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptRecipient | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )

  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithDiscoveryKmsEcdh :=
  set
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var name := keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite)
      )
    
  
  const Tests := 
    AllPostiveKeyringTestsNoDBESuiteNoReqECNoEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteNoReqECWithEphemeralRawEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticRawEcdh
    // + AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticDiscoveryRawEcdh
    // + AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticKmsEcdh
    // + AllPostiveKeyringTestsNoDBESuiteNoReqECWithDiscoveryKmsEcdh
    
}