// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AwsCryptographicMaterialProviders.dfy"

module {:extern "Dafny.Aws.Esdk"} Aws.Esdk {
    import Crypto
    import opened UInt = StandardLibrary.UInt
    import opened Wrappers

    datatype EncryptInput = EncryptInput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext, // TODO Make an option?
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager,
        nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
        nameonly frameLength: Option<int64>,
        nameonly maxPlaintextLength: Option<int64>
        // TODO reintroduce optional materialsManager and optional keyring
    )

    datatype EncryptOutput = EncryptOutput(
        nameonly ciphertext: seq<uint8>
        // TODO Hook up additional Encryption outputs
        // nameonly encryptionContext: Crypto.EncryptionContext,
        // nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    datatype DecryptInput = DecryptInput(
        nameonly ciphertext: seq<uint8>,
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager
        // TODO reintroduce optional and keyring
    )

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>
        // TODO hook up additional decrypt outputs
        // nameonly encryptionContext: Crypto.EncryptionContext,
        // nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
        nameonly commitmentPolicy: Option<Crypto.CommitmentPolicy>,
        //nameonly maxEncryptedEdks: int,
        nameonly configDefaults: ConfigurationDefaults
    )

    datatype ConfigurationDefaults = V1

    trait {:termination false} IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>)
    }
}
