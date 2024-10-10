// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"

module {:options "/functionSyntax:4" } AllEsdkV4WithReqEc {
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
  import AllEsdkV4NoReqEc

  import UUID
  import UTF8
  import JSON.API
  import SortedSets
  import FileIO
  
  // This is a HACK!
  // This is *ONLY* because this is wrapping the MPL
  import AlgorithmSuites

  datatype PositiveESDKDescriptionJSON = PositiveESDKDescriptionJSON(
    description: string,
    inputEncryptionContext: string,
    requiredEncryptionContextKeys: string,
    reproducedEncryptionContext: string,
    encrypt: JSON,
    decrypt: JSON
  )

  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

  const AllSmallEncryptionContextVariants := ["A", "AB", "BA"]
  const RequiredEncryptionContextKeys := ["A", "B"]

  const AllReqECCmmInfo :=
    set
      ec <- AllSmallEncryptionContextVariants,
      requiredKeys <- RequiredEncryptionContextKeys
      ::
        var cmmOnEncryptDescription := Object([
                                                ("type", String("Required Encryption Context CMM")),
                                                ("Input Encryption Context", String(ec)),
                                                ("Required Encryption Context Keys", String(requiredKeys))
                                              ]);
        var cmmOnDecryptDescription := Object([
                                                ("type", String("Required Encryption Context CMM")),
                                                ("Reproduced Encryption Context", String(ec)),
                                                ("Required Encryption Context Keys", String(requiredKeys))
                                              ]);
        PositiveESDKDescriptionJSON(
          description := "Generated with Required Encryption Context Keys " + requiredKeys,
          inputEncryptionContext := ec,
          requiredEncryptionContextKeys := requiredKeys,
          reproducedEncryptionContext := ec,
          encrypt := cmmOnEncryptDescription,
          decrypt := cmmOnDecryptDescription
        )
  
  const frameSize: int64 := 512
  
  function getSmallEC(ec: string)
    : (ecMap: mplTypes.EncryptionContext)
  {
      match ec
      case "A" =>
        map[UTF8.EncodeAscii("keyA") := UTF8.EncodeAscii("valA")]
      case "AB" =>
        map[UTF8.EncodeAscii("keyA") := UTF8.EncodeAscii("valA"),
            UTF8.EncodeAscii("keyB") := UTF8.EncodeAscii("valB")]
      case "BA" =>
        map[UTF8.EncodeAscii("keyB") := UTF8.EncodeAscii("valB"),
            UTF8.EncodeAscii("keyA") := UTF8.EncodeAscii("valA")]
      case _ =>
        map[]
  }


  // All these tests will use a required encryption context CMM no ECDH
  const AllPostiveKeyringTestsNoDBESuiteWithReqECNoEcdh :=
  set
    positiveCMMDescription <- AllReqECCmmInfo,
    postiveKeyDescription <- AllEsdkV4NoReqEc.AllPositiveKeyDescriptions,
    algorithmSuite <-
      AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(postiveKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 4,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [postiveKeyDescription],
        decryptDescriptions := [postiveKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )
  
  // All these tests will use a required encryption context CMM only raw ECDH
  const AllPostiveKeyringTestsNoDBESuiteWithReqECWithEphemeralRawEcdh :=
  set
    positiveCMMDescription <- AllReqECCmmInfo,
    encryptKeyDescription <- AllRawECDH.EphemeralKeyDescriptionsEncrypt,
    decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
    algorithmSuite <- AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )
  
  const AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticRawEcdh :=
  set
      positiveCMMDescription <- AllReqECCmmInfo,
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.RecipientKeyDescriptions | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
      algorithmSuite <- AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )
  
  const AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticDiscoveryRawEcdh :=
  set
      positiveCMMDescription <- AllReqECCmmInfo,
      encryptKeyDescription <- AllRawECDH.SenderKeyDescriptions,
      decryptKeyDescription <- AllRawECDH.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.ECDH.curveSpec == encryptKeyDescription.ECDH.curveSpec,
      algorithmSuite <- AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )
  
  // All these tests will use a required encryption context CMM only KMS ECDH
  const AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticKmsEcdh :=
  set
      positiveCMMDescription <- AllReqECCmmInfo,
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptRecipient | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
      algorithmSuite <- AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )

  const AllPostiveKeyringTestsNoDBESuiteWithReqECWithDiscoveryKmsEcdh :=
  set
      positiveCMMDescription <- AllReqECCmmInfo,
      encryptKeyDescription <- AllKmsEcdh.StaticKmsDescriptionsEncryptSender,
      decryptKeyDescription <- AllKmsEcdh.DiscoveryKeyDescriptionsDecrypt | decryptKeyDescription.KmsECDH.curveSpec == encryptKeyDescription.KmsECDH.curveSpec,
      algorithmSuite <- AllAlgorithmSuites.ESDKAlgorithmSuites
    ::
      var ec := getSmallEC(positiveCMMDescription.inputEncryptionContext);
      var name := AllEsdkV4NoReqEc.keyDescriptionToName(encryptKeyDescription);
      EsdkTestVectors.PositiveEncryptTestVector(
        name := name,
        version := 5,
        manifestPath := "",
        decryptManifestPath := "",
        plaintextPath := "",
        encryptDescriptions := [encryptKeyDescription],
        decryptDescriptions := [decryptKeyDescription],
        encryptionContext := Some(ec),
        decryptEncryptionContext := Some(ec),
        frameLength := Some(frameSize),
        algorithmSuiteId := Some(algorithmSuite),
        cmm := Some("RequiredEncryptionContext")
      )
  
  const Tests := 
    AllPostiveKeyringTestsNoDBESuiteWithReqECNoEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteWithReqECWithEphemeralRawEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticRawEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticDiscoveryRawEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteWithReqECWithStaticKmsEcdh 
    // + AllPostiveKeyringTestsNoDBESuiteWithReqECWithDiscoveryKmsEcdh
    
}