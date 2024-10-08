// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"

module {:options "/functionSyntax:4" } AllEsdkV4NoReqEc {
  import Types = AwsCryptographyEncryptionSdkTypes
  import mplTypes = AwsCryptographyMaterialProvidersTypes
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

  // All these tests will use a defualt CMM no ECDH
  const AllPostiveKeyringTestsNoDBESuiteNoReqECNoEcdh :=
  set
    postiveKeyDescription <- AllPositiveKeyDescriptions,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [postiveKeyDescription],
        decryptDescriptions := [postiveKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )
  
  // All these tests will use a defualt CMM only Raw ECDH
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithEphemeralRawEcdh :=
  set
    encryptKeyDescription <- AllRawECDH.EphemeralKeyDescriptionsEncrypt,
    decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticRawEcdh :=
  set
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.RecipientKeyDescriptions | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticDiscoveryRawEcdh :=
  set
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )
  
  // All these tests will use a defualt CMM only Kms ECDH
  
  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticKmsEcdh :=
  set
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptRecipient | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )

  const AllPostiveKeyringTestsNoDBESuiteNoReqECWithDiscoveryKmsEcdh :=
  set
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      EsdkTestVectors.PositiveEncryptTestVectorV4(
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := None,
        decryptEncryptionContext := None,
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite.id.ESDK)
      )
    
  
  const Tests := 
    AllPostiveKeyringTestsNoDBESuiteNoReqECNoEcdh + 
    AllPostiveKeyringTestsNoDBESuiteNoReqECWithEphemeralRawEcdh +
    AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticRawEcdh +
    AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticDiscoveryRawEcdh +
    AllPostiveKeyringTestsNoDBESuiteNoReqECWithStaticKmsEcdh +
    AllPostiveKeyringTestsNoDBESuiteNoReqECWithDiscoveryKmsEcdh
    
}