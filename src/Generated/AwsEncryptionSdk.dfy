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
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuiteID: Option<Crypto.AlgorithmSuite>,
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager
    )
    {
        predicate Valid() {
            true 
        }
    }

    datatype EncryptOutput = EncryptOutput(
        nameonly ciphertext: seq<uint8>
        //nameonly encryptionContext: Crypto.EncryptionContext,
        //nameonly algorithmSuite: Crypto.AlgorithmSuite
    )
    {
        predicate Valid() {
            true 
        }
    }

    datatype DecryptInput = DecryptInput(
        nameonly ciphertext: seq<uint8>,
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager
        // TODO re introduce optional and keyring
    )
    {
        predicate Valid() {
            true 
        }
    }

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>
        //nameonly encryptionContext: Crypto.EncryptionContext,
        //nameonly algorithmSuite: Crypto.AlgorithmSuite
    )
    {
        predicate Valid() {
            true 
        }
    }

    datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
        // nameonly commitmentPolicy: string,
        // nameonly maxEncryptedEdks: int,
        nameonly configDefaults: string
    )
    {
        predicate Valid() {
            true
        }
    }

    trait {:termination false} IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
            requires input.Valid()
            ensures input.materialsManager.Valid()
        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>)
            requires input.Valid()
            ensures input.materialsManager.Valid()
        // TODO I can't seem to find a way to get this to work
        static method {:extern "createClient"} createClient(clientConfig: AwsEncryptionSdkClientConfig) returns (res: IAwsEncryptionSdkClient)
    }
}