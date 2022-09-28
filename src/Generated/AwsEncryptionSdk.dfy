// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AwsCryptographicMaterialProviders.dfy"

module {:extern "Dafny.Aws.EncryptionSdk"} Aws.Esdk {
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
    nameonly encryptionContext: Option<Crypto.EncryptionContext>,
    nameonly materialsManager: Option<Crypto.ICryptographicMaterialsManager>,
    nameonly keyring: Option<Crypto.IKeyring>,

    //= compliance/client-apis/encrypt.txt#2.4
    //# The following inputs to this behavior MUST be OPTIONAL:
    //# *  Algorithm Suite (Section 2.4.5)
    //# *  Encryption Context (Section 2.4.2)
    //# *  Frame Length (Section 2.4.6)
    nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
    nameonly frameLength: Option<int64>
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

  //= compliance/client-apis/decrypt.txt#2.5
  //= type=implication
  //# The client MUST require the following as inputs to this operation:
  //#*  Encrypted Message (Section 2.5.1)

  //= compliance/client-apis/decrypt.txt#2.5.1
  //= type=implication
  //# The input encrypted message MUST
  //# be a sequence of bytes in the message format (../data-format/
  //# message.md) specified by the AWS Encryption SDK.
  // The above is a little silly. We do not validate that input is
  // an ESDK message, but fail to Decrypt if it is not.
  // TODO: Update Spec accordingly
  datatype DecryptInput = DecryptInput(
    nameonly ciphertext: seq<uint8>,
    nameonly materialsManager: Option<Crypto.ICryptographicMaterialsManager>,
    nameonly keyring: Option<Crypto.IKeyring>
  )

  //= compliance/client-apis/decrypt.txt#2.6
  //= type=implication
  //# The client MUST return as output to this operation:
  //#*  Section 2.6.1
  //#*  Encryption Context (Section 2.6.2)
  //#*  Algorithm Suite (Section 2.6.3)

  //= compliance/client-apis/decrypt.txt#2.6.2
  //= type=exception
  //# This output MAY be satisfied by outputting a parsed header
  //# (Section 2.6.4) containing this value.
  // Where This is the Encryption Context. We do not return
  // a Parsed Header, but we do return the Encryption Context

  //= compliance/client-apis/decrypt.txt#2.6.3
  //= type=exception
  //# This output MAY be satisfied by outputting a parsed header
  //# (Section 2.6.4) containing this value.
  // Where This is the Algorithm Suite. We do not return
  // a Parsed Header, but we do return the Algorithm Suite

  //= compliance/client-apis/decrypt.txt#2.6
  //= type=exception
  //# The client SHOULD return as an output:
  //#*  Parsed Header (Section 2.6.4)
  datatype DecryptOutput = DecryptOutput(
    nameonly plaintext: seq<uint8>,
    nameonly encryptionContext: Crypto.EncryptionContext,
    nameonly algorithmSuiteId: Crypto.AlgorithmSuiteId
  )

  datatype AwsEncryptionSdkConfig = AwsEncryptionSdkConfig(
    nameonly commitmentPolicy: Option<Crypto.CommitmentPolicy>,
    nameonly maxEncryptedDataKeys: Option<int64>
  )

  trait {:termination false} IAwsEncryptionSdkFactory {
    method CreateAwsEncryptionSdk(input: AwsEncryptionSdkConfig) returns (res: Result<IAwsEncryptionSdk, IAwsEncryptionSdkException>)
    method CreateDefaultAwsEncryptionSdk() returns (res: Result<IAwsEncryptionSdk, IAwsEncryptionSdkException>)
  }

  trait {:termination false} IAwsEncryptionSdk {
    method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, IAwsEncryptionSdkException>)
    method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, IAwsEncryptionSdkException>)
  }

  trait IAwsEncryptionSdkException {
    function method GetMessage(): (message: string)
      reads this
  }

  class AwsEncryptionSdkBaseException extends IAwsEncryptionSdkException {
    var message: string

    constructor (message: string) {
      this.message := message;
    }

    function method GetMessage(): (message: string)
      reads this
    {
      this.message
    }
  }

  class AwsEncryptionSdkException extends IAwsEncryptionSdkException {
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
          var wrappedError := new AwsEncryptionSdkException(error);
          return Result.Failure(wrappedError);
      }
    }
  }
}
