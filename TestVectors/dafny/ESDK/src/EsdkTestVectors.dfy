// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"

module {:options "-functionSyntax:4"} EsdkTestVectors {
  import Types = AwsCryptographyEncryptionSdkTypes
  import mplTypes = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders
  import WrappedESDK

  import opened Wrappers
  import opened StandardLibrary.UInt
  import UTF8
  import FileIO
  import UUID

  import opened JSONHelpers
  import KeyVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import TestVectors

  datatype EncryptTest = EncryptTest(
    cmm: mplTypes.ICryptographicMaterialsManager,
    client: Types.IAwsEncryptionSdkClient,
    vector: EsdkEncryptTestVector
  )
  {
    ghost predicate ValidState()
    {
      && cmm.ValidState()
      && client.ValidState()
      && cmm.Modifies !! {client.History}
    }
  }

  datatype DecryptTest = DecryptTest(
    cmm: mplTypes.ICryptographicMaterialsManager,
    client: Types.IAwsEncryptionSdkClient,
    vector: EsdkDecryptTestVector
  )
  {
    ghost predicate ValidState()
    {
      && cmm.ValidState()
      && client.ValidState()
      && cmm.Modifies !! {client.History}
    }
  }
  
  type SupportedGenerateManifestVersion = v: nat | SupportedGenerateManifestVersion?(v) witness 4
  predicate SupportedGenerateManifestVersion?(v: nat)
  {
    || v == 4
  } 

  type SupportedEncryptVersion = v: nat | SupportedEncryptVersion?(v)  witness 1
  predicate SupportedEncryptVersion?(v: nat)
  {
    || v == 1
  }


  datatype EsdkEncryptTestVector =
    | PositiveEncryptTestVector(
        name: string,
        version: SupportedEncryptVersion,
        manifestPath: string,
        decryptManifestPath: string,
        plaintextPath: string,
        encryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        decryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        decryptEncryptionContext: Option<mplTypes.EncryptionContext> := None,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        frameLength: Option<int64>,
        algorithmSuiteId: Option<mplTypes.ESDKAlgorithmSuiteId>
      )
    | PositiveEncryptTestVectorV4(
        encryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        decryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        decryptEncryptionContext: Option<mplTypes.EncryptionContext> := None,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        frameLength: Option<int64>,
        algorithmSuiteId: Option<mplTypes.ESDKAlgorithmSuiteId>
      )
    | PositiveEncryptNegativeDecryptTestVector (
        name: string,
        version: SupportedEncryptVersion,
        manifestPath: string,
        decryptManifestPath: string,
        plaintextPath: string,
        encryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        decryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        decryptEncryptionContext: Option<mplTypes.EncryptionContext> := None,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        frameLength: Option<int64>,
        algorithmSuiteId: Option<mplTypes.ESDKAlgorithmSuiteId>,
        decryptErrorDescription: string
      )
    | NegativeEncryptTestVector(
        name: string,
        version: SupportedEncryptVersion,
        manifestPath: string,
        plaintextPath: string,
        encryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        frameLength: Option<int64>,
        algorithmSuiteId: Option<mplTypes.ESDKAlgorithmSuiteId>,
        errorDescription: string
      )

  type SupportedDecryptVersion = v: nat | SupportedDecryptVersion?(v)  witness 1
  predicate SupportedDecryptVersion?(v: nat)
  {
    || v == 1
    || v == 2
  }

  datatype EsdkDecryptTestVector =
    | PositiveDecryptTestVector(
        name: string,
        version: SupportedDecryptVersion,
        manifestPath: string,
        ciphertextPath: string,
        plaintextPath: string,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        decryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        decryptionMethod: DecryptionMethod
      )
    | NegativeDecryptTestVector(
        name: string,
        version: SupportedDecryptVersion,
        manifestPath: string,
        ciphertextPath: string,
        errorDescription: string,
        encryptionContext: Option<mplTypes.EncryptionContext> := None,
        decryptDescriptions: seq<KeyVectorsTypes.KeyDescription>,
        commitmentPolicy: mplTypes.ESDKCommitmentPolicy := mplTypes.FORBID_ENCRYPT_ALLOW_DECRYPT,
        decryptionMethod: DecryptionMethod
      )

  datatype DecryptionMethod =
    | StreamingUnsignedOnly
    | OneShot

  method TestDecrypt(
    keys: KeyVectors.KeyVectorsClient,
    vector: EsdkDecryptTestVector
  )
    returns (output: bool)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
  {
    print "\nTEST===> ", vector.name, "\n";

    // The decrypt test vectors also test initialization
    // This is because they were developed when the MPL
    // was still part of the ESDK
    var maybeTest := DecryptVectorToDecryptTest(keys, vector);
    if maybeTest.Success? {
      var test := maybeTest.value;

      var ciphertext :- expect ReadVectorsFile(test.vector.manifestPath + test.vector.ciphertextPath);
      var plaintext;
      if test.vector.PositiveDecryptTestVector? {
        plaintext :- expect ReadVectorsFile(test.vector.manifestPath + test.vector.plaintextPath);
      }

      var input := Types.DecryptInput(
        ciphertext := ciphertext,
        encryptionContext := test.vector.encryptionContext,
        materialsManager := Some(test.cmm),
        keyring := None
      );

      var result := test.client.Decrypt(input);

      output := match test.vector
        case PositiveDecryptTestVector(_,_,_,_,_,_,_,_,_)
          =>
          && result.Success?
          && result.value.plaintext == plaintext
        case NegativeDecryptTestVector(_,_,_,_,_,_,_,_,_)
          =>
          && result.Failure?;
      if !output {
        if test.vector.PositiveDecryptTestVector? && result.Failure? {
          print result.error, "\n";
          if
            && result.error.AwsCryptographyMaterialProviders?
            && result.error.AwsCryptographyMaterialProviders.CollectionOfErrors?
          {
            print "list:", result.error.AwsCryptographyMaterialProviders.list, "\n";
          }
        }
        print "\nFAILED! <-----------\n";
      }
    } else {
      output := match vector
        case PositiveDecryptTestVector(_,_,_,_,_,_,_,_,_)
          => false
        case NegativeDecryptTestVector(_,_,_,_,_,_,_,_,_)
          => true;

      if !output {
        if vector.PositiveDecryptTestVector? && maybeTest.Failure? {
          print maybeTest.error;
        }
        print "\nFAILED! <-----------\n";
      }
    }
  }

  method DecryptVectorToDecryptTest(
    keys: KeyVectors.KeyVectorsClient,
    vector: EsdkDecryptTestVector
  )
    returns (output: Result<DecryptTest, KeyVectorsTypes.Error>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()

    ensures output.Success?
            ==>
              && output.value.ValidState()
              && fresh(output.value.cmm.Modifies - keys.Modifies)
              && fresh(output.value.client.Modifies)
  {
    var cmm :- KeyDescriptionToCmm(keys, vector.decryptDescriptions);

    var config := WrappedESDK.WrappedAwsEncryptionSdkConfigWithSuppliedCommitment(
      commitmentPolicy := vector.commitmentPolicy
    );

    var client :- expect WrappedESDK.WrappedESDK(config := config);

    var test := DecryptTest(
      cmm := cmm,
      client := client,
      vector := vector
    );

    output := Success(test);
  }

  const plaintextPathRoot := "plaintexts/"
  const ciphertextPathPathRoot := "ciphertexts/"

  datatype EncryptTestOutput = EncryptTestOutput(
    output: bool,
    vector: Option<EsdkDecryptTestVector> := None
  )

  method TestEncrypt(
    plaintexts: map<string, seq<uint8>>,
    keys: KeyVectors.KeyVectorsClient,
    vector: EsdkEncryptTestVector
  )
    returns (output: EncryptTestOutput)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()

    requires vector.frameLength.Some? ==> Types.IsValid_FrameLength(vector.frameLength.value)
  {
    print "\nTEST===> ", vector.name, "\n";

    // The decrypt test vectors also test initialization
    // This is because they were developed when the MPL
    // was still part of the ESDK
    var maybeTest := EncryptVectorToEncryptTest(keys, vector);
    if maybeTest.Success? {
      var test := maybeTest.value;

      expect test.vector.plaintextPath in plaintexts;
      var plaintext := plaintexts[test.vector.plaintextPath];
      var frameLength: Option<Types.FrameLength> := vector.frameLength;

      var input := Types.EncryptInput(
        plaintext := plaintext,
        encryptionContext := test.vector.encryptionContext,
        materialsManager := Some(test.cmm),
        keyring := None,
        frameLength := frameLength,
        algorithmSuiteId := test.vector.algorithmSuiteId
      );
      var result := test.client.Encrypt(input);

      if
        && result.Success?
        && (
             || test.vector.PositiveEncryptTestVector?
             || test.vector.PositiveEncryptNegativeDecryptTestVector?
           )
      {
        var name :- expect UUID.GenerateUUID();
        var decryptVector := EncryptTestToDecryptVector(name, test, result.value);
        output := EncryptTestOutput(
          vector := Some(decryptVector),
          output := true
        );
      } else if result.Failure? && test.vector.NegativeEncryptTestVector? {
        output := EncryptTestOutput( output := true );
      } else {
        output := EncryptTestOutput( output := false );
        if !test.vector.NegativeEncryptTestVector? && result.Failure? {
          print result.error;
        }
        print "\nFAILED! <-----------\n";
      }
    } else {
      if maybeTest.Failure? ==> vector.NegativeEncryptTestVector?
      {
        output := EncryptTestOutput( output := true );
      } else {
        output := EncryptTestOutput( output := false );
        if !vector.NegativeEncryptTestVector? && maybeTest.Failure? {
          print maybeTest.error;
        }
        print "\nFAILED! <-----------\n";
      }
    }
  }

  method EncryptVectorToEncryptTest(
    keys: KeyVectors.KeyVectorsClient,
    vector: EsdkEncryptTestVector
  )
    returns (output: Result<EncryptTest, KeyVectorsTypes.Error>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()

    ensures output.Success?
            ==>
              && output.value.ValidState()
              && fresh(output.value.cmm.Modifies - keys.Modifies)
              && fresh(output.value.client.Modifies)
  {
    var cmm :- KeyDescriptionToCmm(keys, vector.encryptDescriptions);

    var config := WrappedESDK.WrappedAwsEncryptionSdkConfigWithSuppliedCommitment(
      commitmentPolicy := vector.commitmentPolicy
    );

    var client :- expect WrappedESDK.WrappedESDK(config := config);

    var test := EncryptTest(
      cmm := cmm,
      client := client,
      vector := vector
    );

    output := Success(test);
  }

  method EncryptTestToDecryptVector(
    name: string,
    test: EncryptTest,
    result: Types.EncryptOutput
  ) returns (output: EsdkDecryptTestVector)
    requires
      || test.vector.PositiveEncryptTestVector?
      || test.vector.PositiveEncryptNegativeDecryptTestVector?
  {
    output := match test.vector
      case PositiveEncryptTestVector(_,_,_,_,_,_,_,_,_,_,_,_) =>
        PositiveDecryptTestVector(
          name := name,
          version := 2,
          manifestPath := test.vector.decryptManifestPath,
          ciphertextPath := ciphertextPathPathRoot + name,
          plaintextPath := plaintextPathRoot + test.vector.plaintextPath,
          encryptionContext := test.vector.decryptEncryptionContext,
          decryptDescriptions := test.vector.decryptDescriptions,
          commitmentPolicy := test.vector.commitmentPolicy,
          decryptionMethod := DecryptionMethod.OneShot
        )

      case PositiveEncryptNegativeDecryptTestVector(_,_,_,_,_,_,_,_,_,_,_,_,_) =>
        NegativeDecryptTestVector(
          name := name,
          version := 2,
          manifestPath := test.vector.decryptManifestPath,
          ciphertextPath := ciphertextPathPathRoot + name,
          errorDescription := test.vector.decryptErrorDescription,
          encryptionContext := test.vector.decryptEncryptionContext,
          decryptDescriptions := test.vector.decryptDescriptions,
          commitmentPolicy := test.vector.commitmentPolicy,
          decryptionMethod := DecryptionMethod.OneShot
        );

    var decryptManifestCiphertext := test.vector.decryptManifestPath + ciphertextPathPathRoot + name;
    // Side effect, to avoid thousands of ciphertext in memory...
    var _ :- expect WriteVectorsFile(decryptManifestCiphertext, result.ciphertext);
  }


  function MplPrintErr(e: mplTypes.Error) : (){()} by method {print e, "\n", "\n"; return ();}


  method KeyDescriptionToCmm(
    keys: KeyVectors.KeyVectorsClient,
    keyDescriptions: seq<KeyVectorsTypes.KeyDescription>
  )
    returns (output: Result<mplTypes.ICryptographicMaterialsManager, KeyVectorsTypes.Error>)

    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()

    ensures output.Success?
            ==>
              && fresh(output.value.Modifies - keys.Modifies)
              && output.value.ValidState()
  {
    var keyringList: seq<mplTypes.IKeyring> := [];
    for i := 0 to |keyDescriptions|
      invariant forall k | k in keyringList ::
          && k.ValidState() && fresh(k.Modifies)
      invariant forall k | k in keyringList
          :: k.Modifies
             <= set m: object, k :mplTypes.IKeyring
                  |
                  && k in keyringList
                  && m in k.Modifies
                  :: m
    {
      var keyDescription := keyDescriptions[i];
      var keyring :- keys.CreateWrappedTestVectorKeyring(
        KeyVectorsTypes.TestVectorKeyringInput(
          keyDescription := keyDescription
        ));
      keyringList := keyringList + [keyring];
    }

    :- Need(|keyringList| > 0, KeyVectorsTypes.KeyVectorException( message := "Failed to create any keyrings" ));
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var generatorKeyring := keyringList[0];
    var maybeMultiKeyring := mpl.CreateMultiKeyring(
      mplTypes.CreateMultiKeyringInput(
        generator := Some(generatorKeyring),
        childKeyrings := keyringList[1..]
      )
    );

    var keyring :- maybeMultiKeyring
    .MapFailure(e => KeyVectorsTypes.AwsCryptographyMaterialProviders(e));

    var maybeCmm := mpl
    .CreateDefaultCryptographicMaterialsManager(
      mplTypes.CreateDefaultCryptographicMaterialsManagerInput( keyring := maybeMultiKeyring.value )
    );
    output := maybeCmm
    .MapFailure(e => KeyVectorsTypes.AwsCryptographyMaterialProviders(e));
  }

  method ReadVectorsFile(location: string)
    returns (output: Result<seq<uint8>, string>)
  {
    var fileBv :- FileIO.ReadBytesFromFile(location);
    output := Success(BvToBytes(fileBv));
  }

  method WriteVectorsFile(location: string, bytes: seq<uint8>)
    returns (output: Result<(), string>)
  {
    var bv := BytesBv(bytes);
    output := FileIO.WriteBytesToFile(location, bv);
  }
}
