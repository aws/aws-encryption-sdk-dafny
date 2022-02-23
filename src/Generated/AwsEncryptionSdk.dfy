// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AwsCryptographicMaterialProviders.dfy"

module {:extern "Dafny.Aws.Esdk"} Aws.Esdk {
    import Crypto
    import opened UInt = StandardLibrary.UInt
    import opened Wrappers

    // TODO: All annotations in this file should probably eventually go on
    // the smithy model, since that's the authority and this code will be
    // auto-generated

    datatype EncryptInput = EncryptInput(
        //= compliance/client-apis/encrypt.txt#2.4
        //= type=implication
        //# The following inputs to this behavior are REQUIRED:
        //# *  Plaintext (Section 2.4.1)

        //= compliance/client-apis/encrypt.txt#2.4.1
        //= type=implication
        //# This MUST be a sequence of bytes.
        nameonly plaintext: seq<uint8>,
        nameonly materialsManager: Option<Crypto.ICryptographicMaterialsManager>,
        nameonly keyring: Option<Crypto.IKeyring>,

        //= compliance/client-apis/encrypt.txt#2.4
        //= type=TODO
        //# The following inputs to this behavior MUST be OPTIONAL:
        //# *  Algorithm Suite (Section 2.4.5)
        //# *  Encryption Context (Section 2.4.2)
        //# *  Frame Length (Section 2.4.6)
        // Marked as TODO because EC is not optional yet
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
        nameonly frameLength: Option<int64>,

        // TODO: remove, since streaming is not yet supported
        nameonly maxPlaintextLength: Option<int64>
    )

    datatype EncryptOutput = EncryptOutput(
        //= compliance/client-apis/encrypt.txt#2.5.1
        //# This MUST
        //# be a sequence of bytes and conform to the message format
        //# specification (../data-format/message.md).
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
