// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "VectorsComposition/AllEsdkV4NoReqEc.dfy"

module {:options "-functionSyntax:4"} WriteVectors {
  import Types = AwsCryptographyEncryptionSdkTypes
  import mplTypes = AwsCryptographyMaterialProvidersTypes
  import EncryptionSdk
  import MaterialProviders
  import opened CompleteVectors
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


  function GetCommitmentPolicyString(algorithmSuite: mplTypes.AlgorithmSuiteInfo)
    : (commitmentPolicy: string)
  {
    match algorithmSuite.id
    case ESDK(_) =>
      if algorithmSuite.commitment.None? then
        "FORBID_ENCRYPT_ALLOW_DECRYPT"
      else
        "REQUIRE_ENCRYPT_REQUIRE_DECRYPT"
    case DBE(_) => "NOT SUPPORTED FOR UNSTRUCTURED ENCRYPTION"
  }

  function GetCommitmentPolicyType(commitmentPolicy: string)
    : (commitmentPolicyType: mplTypes.CommitmentPolicy)
  {
    if commitmentPolicy == "FORBID_ENCRYPT_ALLOW_DECRYPT" then
      mplTypes.CommitmentPolicy.ESDK(mplTypes.ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT)
    else
      mplTypes.CommitmentPolicy.ESDK(mplTypes.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
  }

  // This will be helpful when encrypting and decrypting, come back
  // function getSmallEC(ec: string)
  //     : (ecMap: Result<mplTypes.EncryptionContext, string>)
  // {
  //     match ec
  //     case "A" =>
  //         var m := JSONHelpers.utf8EncodeMap(map["keyA" := "valA"]);
  //         :- Need(m.Success?, "Unable to create Encryption Context map");
  //         Success(m.value)
  //     case "AB" =>
  //         var m := JSONHelpers.utf8EncodeMap(map["keyA" := "valA", "keyB" := "valB"]);
  //         :- Need(m.Success?, "Unable to create Encryption Context map");
  //         Success(m.value)
  //     case "BA" =>
  //         var m := JSONHelpers.utf8EncodeMap(map["keyB" := "valB", "keyA" := "valA"]);
  //         :- Need(m.Success?, "Unable to create Encryption Context map");
  //         Success(m.value)
  // }

  const AllPositiveKeyringTestsNoDBESuiteWithReqEC: set<JSON> := {}
  // set
  //   positiveCMMDescription <-
  //     AllReqECCmmInfo,
  //   postiveKeyDescription <-
  //     AllKMSInfo +
  //     AllKmsMrkAware +
  //     AllKmsMrkAwareDiscovery +
  //     AllRawAES +
  //     AllRawRSA +
  //     AllHierarchy +
  //     AllKmsRsa,
  //   algorithmSuite <-
  //     ESDKAlgorithmSuites
  //     // AwsKmsRsaKeyring cannot be used with an Algorithm Suite with asymmetric signing
  //   | !(postiveKeyDescription.description[..|KmsRsa|] == KmsRsa && algorithmSuite.signature.ECDSA?)
  //   ::
  //     var id := HexStrings.ToHexString(algorithmSuite.binaryId);
  //     var commitmentPolicy := GetCommitmentPolicyString(algorithmSuite);
  //     Object([
  //              ("type", String("positive-esdk")),
  //              ("message", String("asdf")),
  //              ("required ec cmm description", String(positiveCMMDescription.description)),
  //              ("keyring description", String(postiveKeyDescription.description + " " + id)),
  //              ("clientCommitmentPolicy", String(commitmentPolicy)),
  //              ("algorithmSuiteId", String(id)),
  //              ("encryptionContext", String(positiveCMMDescription.inputEncryptionContext)),
  //              ("requiredEncryptionContextKeys", Array([String(positiveCMMDescription.requiredEncryptionContextKeys)])),
  //              ("encryptKeyDescription", postiveKeyDescription.encrypt),
  //              ("decryptKeyDescription", postiveKeyDescription.decrypt)
  //            ])



  method WritetestVectors(op: EsdkManifestOptions.ManifestOptions)
    returns (output: Result<(), string>)
    requires op.EncryptManifest?
  {
    var version := op.version;
    var allTests :- getVersionTests(version);

    var tests := SortedSets.ComputeSetToSequence(allTests);

    // var tests := testsNoReqEC;
    var testsJSON: seq<(string, JSON)> := [];

    for i := 0 to |tests|
    {
      // var name :- expect UUID.GenerateUUID();
      // var testVector := EsdkTestVectors.PositiveEncryptTestVector(
      //   name := "Positive Encrypt Test Vector-" + name,
      //   version := tests[i].version,
      //   manifestPath := op.manifestPath,
      //   decryptManifestPath := op.decryptManifestOutput,
      //   plaintextPath := string,

      // );
      // tests[i].name := tests[i].name + name;

      // testsJSON := testsJSON + [(name, tests[i])];
    }

    var esdkEncryptManifests := Object(
      [
        ("tests", Object(testsJSON))
      ]
    );

    var esdkEncryptManifestBytes :- expect API.Serialize(esdkEncryptManifests);
    var esdkEncryptManifestBv := JSONHelpers.BytesBv(esdkEncryptManifestBytes);

    var _ :- expect FileIO.WriteBytesToFile(
      op.encryptManifestOutput + "manifest.json",
      esdkEncryptManifestBv
    );
    
    output := Success(());
  }

  function getVersionTests(version: nat): (ret: Result<set<EsdkTestVectors.EsdkEncryptTestVector>, string>)
  {
    match version
      case 4 => Success(AllEsdkV4NoReqEc.Tests)
      case _ => Failure("Only version 4 of generate manifest is supported\n")
  }
}