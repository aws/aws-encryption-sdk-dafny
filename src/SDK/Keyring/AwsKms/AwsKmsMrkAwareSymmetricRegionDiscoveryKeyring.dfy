// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Defs.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuite.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../../libraries/src/Closures.dfy"

module {:extern "AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring"} AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Closures
  import AlgorithmSuite
  import KeyringDefs
  import Materials
  import KMSUtils
  import UTF8

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s

  datatype DiscoveryFilter = DiscoveryFilter(
    partition: string,
    accounts: seq<string>
  )

  class AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring 
    extends KeyringDefs.Keyring
  {

    const client: IAmazonKeyManagementService
    const discoveryFilter: Option<DiscoveryFilter>
    const grantTokens: seq<KMSUtils.GrantToken>

    constructor (
      client: IAmazonKeyManagementService,
      discoveryFilter: Option<DiscoveryFilter>,
      grantTokens: seq<KMSUtils.GrantToken>
    )
    {
      this.client          := client;
      this.discoveryFilter := discoveryFilter;
      this.grantTokens     := grantTokens;
    }

    predicate Valid()
      // reads this, Repr
      // ensures Valid() ==> this in Repr
    {
      true
      // && this in Repr
      // && 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      // && (|keyIDs| == 0 && generator.None? ==> isDiscovery)
      // && (clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid())
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials)
      returns (res: Result<Materials.ValidEncryptionMaterials, string>)
    {
      return Failure("bad");
    }

    method OnDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      edks: seq<Materials.EncryptedDataKey>
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
    {

      if (materials.plaintextDataKey.Some?) {
        return Success(materials);
      }

      var filter := new EncrypteDataKeyFilter(this.discoveryFilter);
      var edksToAttempt :- Closures.Filter(edks, filter);

      var decrypt := new DecryptEncryptedDataKey(
        materials,
        this.client,
        this.grantTokens
      );
      var outcome := Closures.ReduceToSuccess(
        edksToAttempt,
        decrypt
      );

      return match outcome {
        case Success(mat) => Success(mat)
        case Failure(errors) =>
          if |errors| == 0 then
            Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.")
          else 
            var concatString := (s, a) => a + "\n" + s;
            var error := Seq.FoldRight(
              concatString,
              errors,
              "Unable to decrypt data key:\n"
            );
            Failure(error)
      };
    }
  }

  class EncrypteDataKeyFilter 
  extends ActionWithResult<Materials.EncryptedDataKey, bool, string>
  {
    const discoveryFilter: Option<DiscoveryFilter>

    constructor(discoveryFilter: Option<DiscoveryFilter>) {
      this.discoveryFilter := discoveryFilter;
    }

    method Invoke(edk: Materials.EncryptedDataKey
    )
      returns (res: Result<bool, string>)

    {
      var keyId :- UTF8.Decode(edk.providerInfo);
      var arn :- ParseAwsKmsArn(keyId);

      // const asdf := IsMultiRegionAwsKmsArn(arn);

      return Success(
        match this.discoveryFilter {
          case Some(filter) => 
            && filter.partition == arn.partition
            && filter.accounts <= [arn.account]
          case None() => true
        }
      );
    }
  }

  class DecryptEncryptedDataKey
  extends ActionWithResult<
    Materials.EncryptedDataKey,
    Materials.ValidDecryptionMaterials,
    string>
  {
    const materials: Materials.ValidDecryptionMaterials
    const client: IAmazonKeyManagementService
    const grantTokens: seq<KMSUtils.GrantToken>

    constructor(
      materials: Materials.ValidDecryptionMaterials,
      client: IAmazonKeyManagementService,
      grantTokens: seq<KMSUtils.GrantToken>
    ) {
      this.materials := materials;
      this.client := client;
      this.grantTokens := grantTokens;
    }

    method Invoke(
      edk: Materials.EncryptedDataKey
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
    {
      var awsKmsKey :- UTF8.Decode(edk.providerInfo);
      var decryptRequest := KMSUtils.DecryptRequest(
        awsKmsKey,
        edk.ciphertext,
        materials.encryptionContext,
        grantTokens
      );

      var decryptResponse :- KMSUtils.Decrypt(this.client, decryptRequest);

      :- Need(
        && decryptResponse.keyID == awsKmsKey
        && materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext)
        , "Invalid response from KMS Decrypt");

      var result := this.materials.WithPlaintextDataKey(decryptResponse.plaintext);
      return Success(result);
    }
  }
}




  // trait {:termination false} UnwrapSingleEncryptedDataKey {
  //   method Decrypt(
  //     materials: Materials.ValidDecryptionMaterials,
  //     encryptedDataKey: Materials.EncryptedDataKey
  //   ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)

  //   method FirstSuccessufulDecrypt(
  //     materials: Materials.ValidDecryptionMaterials,
  //     encryptedDataKeys: seq<Materials.EncryptedDataKey>,
  //     emptyError: string,
  //     initError: string
  //   ) returns (res: Result<Materials.ValidDecryptionMaterials, string>) {

  //     var errors := [];
  //     for i := 0 to |encryptedDataKeys| {
  //       var thisResult := this.Decrypt(materials, encryptedDataKeys[i]);
  //       if thisResult.Success? {
  //         return Success(thisResult.value);
  //       } else {
  //         errors := errors + [thisResult.error];
  //       }
  //     }

  //     if |errors| == 0 {
  //       return Failure(emptyError);
  //     } else {
  //       var concatString := (s, a) => a + "\n" + s;
  //       var error := FoldRight(
  //         concatString,
  //         errors,
  //         initError
  //       );
  //       return Failure(error);
  //     }
  //   }
  // }