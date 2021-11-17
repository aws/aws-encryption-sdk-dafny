// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../KMS/AmazonKeyManagementService.dfy"
include "AwsCryptographicMaterialProviders.dfy"

module {:extern "Dafny.Aws.Esdk"} Aws.Esdk {
    import Crypto
    import opened UInt = StandardLibrary.UInt
    import opened Wrappers

    datatype EncryptInput = EncryptInput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext, // TODO Make an option?
        // TODO Turn these nullables into Options
        // blocked by https://github.com/dafny-lang/dafny/issues/1499
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager?,
        nameonly keyring: Crypto.IKeyring?,
        nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
        nameonly frameLength: Option<int32>
    )

    datatype EncryptOutput = EncryptOutput(
        nameonly encryptedMessage: seq<uint8> // TODO update smithy model name
        // TODO Hook up additional Encryption outputs
        // nameonly encryptionContext: Crypto.EncryptionContext,
        // nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    datatype DecryptInput = DecryptInput(
        nameonly encryptedMessage: seq<uint8>, // TODO update smithy model name
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager?,
        nameonly keyring: Crypto.IKeyring?
    )

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>
        // TODO hook up additional decrypt outputs
        // nameonly encryptionContext: Crypto.EncryptionContext,
        // nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    // datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
    //     nameonly commitmentPolicy: string,
    //     nameonly maxEncryptedEdks: int,
    //     nameonly configDefaults: ConfigurationDefaults
    // )

    trait {:termination false} IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>)
    }
}
