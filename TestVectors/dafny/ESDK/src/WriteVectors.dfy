// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "VectorsComposition/AllEsdkV4NoReqEc.dfy"
include "VectorsComposition/AllEsdkV4WithReqEc.dfy"
include "WriteEsdkJsonManifests.dfy"

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
  import AllEsdkV4WithReqEc
  import WriteEsdkJsonManifests

  import UUID
  import UTF8
  import JSON.API
  import SortedSets
  import FileIO

  // This is a HACK!
  // This is *ONLY* because this is wrapping the MPL
  import AlgorithmSuites

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

  method WritetestVectors(op: EsdkManifestOptions.ManifestOptions)
    returns (output: Result<(), string>)
    requires op.EncryptManifest?
  {
    var version := op.version;
    var allTests :- getVersionTests(version);

    var tests := SortedSets.ComputeSetToSequence(allTests);

    var testsJSON: seq<(string, JSON)> := [];

    for i := 0 to |tests|
    {
      :- Need(
        && tests[i].algorithmSuiteId.Some?
        && tests[i].cmm.Some?, 
        "No cmm or algorithm suite defined in test"
      );

      var id := AllAlgorithmSuites.ToHex(tests[i].algorithmSuiteId.value);
      var uuid :- expect UUID.GenerateUUID();
      var name := id + "-" + tests[i].name + "-" + tests[i].cmm.value + "-" + uuid;
      var test :- WriteEsdkJsonManifests.EncryptTestVectorToJson(tests[i]);
      testsJSON := testsJSON + [(name, test)];
    }
    
    var manifestJson := Object([
          ("type", String("awses-decrypt-generate")),
          ("version", Number(Int(4)))]);

    var plaintexts := Object([("small", Number(Int(10240)))]);

    var esdkEncryptManifests := Object(
      [
        ("manifest", manifestJson),
        ("keys", String("keys.json")),
        ("plaintexts", plaintexts),
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
      case 4 => Success(AllEsdkV4WithReqEc.Tests + AllEsdkV4NoReqEc.Tests)
      case _ => Failure("Only version 4 of generate manifest is supported\n")
  }
}