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
        //= compliance/client-apis/encrypt.txt#2.4.1
        //= type=implication
        //# This MUST be a sequence of bytes.
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly materialsManager: Option<Crypto.ICryptographicMaterialsManager>,
        nameonly keyring: Option<Crypto.IKeyring>,
        nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
        nameonly frameLength: Option<int64>,
        nameonly maxPlaintextLength: Option<int64>
    )

    datatype EncryptOutput = EncryptOutput(
        nameonly ciphertext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    datatype DecryptInput = DecryptInput(
        nameonly ciphertext: seq<uint8>,
        nameonly materialsManager: Option<Crypto.ICryptographicMaterialsManager>,
        nameonly keyring: Option<Crypto.IKeyring>
    )

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
    )

    datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
        nameonly commitmentPolicy: Option<Crypto.CommitmentPolicy>,
        nameonly maxEncryptedDataKeys: Option<int64>,
        nameonly configDefaults: ConfigurationDefaults
    )

    datatype ConfigurationDefaults = V1

    trait {:termination false} IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, IAwsEncryptionSdkException>)
        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, IAwsEncryptionSdkException>)
    }

    trait IAwsEncryptionSdkException {
        function method GetMessage(): (message: string)
            reads this
    }

    class AwsEncryptionSdkClientException extends IAwsEncryptionSdkException {
        var message: string

        constructor (message: string) {
            this.message := message;
        }

        function method GetMessage(): (message: string)
            reads this
        {
            this.message
        }

        static method WrapResultString<T>(result: Result<T, string>)
            returns (wrapped: Result<T, IAwsEncryptionSdkException>)
            ensures result.Success? ==>
                && wrapped.Success?
                && wrapped.value == result.value
            ensures result.Failure? ==>
                && wrapped.Failure?
        {
            match result {
                case Success(value) => return Result.Success(value);
                case Failure(error) =>
                    var wrappedError := new AwsEncryptionSdkClientException(error);
                    return Result.Failure(wrappedError);
            }
        }
    }
}
