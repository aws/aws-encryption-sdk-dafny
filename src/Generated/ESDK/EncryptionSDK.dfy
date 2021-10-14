include "../../Util/UTF8.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../MaterialProviders/MaterialProviders.dfy"

module {:extern "AwsEncryptionSdk"} EncryptionSDK {
    export provides AwsEncryptionSdkClient, AwsEncryptionSdkClientConfig, AwsEncryptionSdkClient.createClient
    
    import opened Wrappers
    import CryptographicMaterialProviders
    import opened UInt = StandardLibrary.UInt

    datatype EncryptInput = EncryptInput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: Option<CryptographicMaterialProviders.Structures.EncryptionContext>,
        nameonly algorithmSuite: Option<CryptographicMaterialProviders.CryptoConfig.AlgorithmSuite>,
        nameonly keyring: CryptographicMaterialProviders.Keyrings.IKeyring?,
        nameonly materialsManager: CryptographicMaterialProviders.CMMs.ICryptographicMaterialsManager?
    )

    datatype EncryptOutput = EncryptOutput(
        nameonly ciphertext: seq<uint8>,
        nameonly encryptionContext: CryptographicMaterialProviders.Structures.EncryptionContext,
        nameonly algorithmSuite: CryptographicMaterialProviders.CryptoConfig.AlgorithmSuite
    )

    datatype DecryptInput = DecryptInput(
        nameonly ciphertext: seq<uint8>,
        nameonly keyring: CryptographicMaterialProviders.Keyrings.IKeyring?,
        nameonly materialsManager: CryptographicMaterialProviders.CMMs.ICryptographicMaterialsManager?
    )

    datatype DecryptOutput = DecryptOutput(
        nameonly plaintext: seq<uint8>,
        nameonly encryptionContext: CryptographicMaterialProviders.Structures.EncryptionContext,
        nameonly algorithmSuite: CryptographicMaterialProviders.CryptoConfig.AlgorithmSuite
    )

    trait IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
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
    }
}