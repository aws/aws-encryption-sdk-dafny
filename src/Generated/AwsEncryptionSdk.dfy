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
        nameonly encryptionContext: Option<Crypto.EncryptionContext>,
        nameonly algorithmSuite: Option<Crypto.AlgorithmSuite>,
        nameonly keyring: Crypto.IKeyring?,
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager?
    )

    datatype EncryptOutput = EncryptOutput(
        nameonly ciphertext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuite: Crypto.AlgorithmSuite
    )

    datatype DecryptInput = DecryptInput(
        nameonly ciphertext: seq<uint8>,
        nameonly keyring: Crypto.IKeyring?,
        nameonly materialsManager: Crypto.ICryptographicMaterialsManager?
    )

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Crypto.EncryptionContext,
        nameonly algorithmSuite: Crypto.AlgorithmSuite
    )

    trait IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>)
    }

    datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
        nameonly commitmentPolicy: string,
        nameonly maxEncryptedEdks: int,
        nameonly configDefaults: string
    )

    class AwsEncryptionSdkClient extends IAwsEncryptionSdkClient {
        const clientConfig: AwsEncryptionSdkClientConfig

        constructor(clientConfig: AwsEncryptionSdkClientConfig) {
            this.clientConfig := clientConfig;
        }

        static method createClient(nameonly clientConfig: AwsEncryptionSdkClientConfig) returns (res: AwsEncryptionSdkClient) {
            res := new AwsEncryptionSdkClient(clientConfig);
        }

        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>) {
            // TODO
        }

        method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>) {
            // TODO
        }
    }
}