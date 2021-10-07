include "../../Util/UTF8.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../MaterialProviders/MaterialProviders.dfy"

module {:extern "AwsEncryptionSdk"} EncryptionSDK {
    import opened Wrappers
    import CryptographicMaterialProviders
    import opened UInt = StandardLibrary.UInt

    datatype EncryptInput = EncryptInput(
        plaintext: seq<uint8>,
        encryptionContext: Option<CryptographicMaterialProviders.Structures.EncryptionContext>,
        algorithmSuite: Option<string>,
        keyring: CryptographicMaterialProviders.Keyrings.IKeyring?,
        materialsManager: CryptographicMaterialProviders.CMMs.ICryptographicMaterialProvider?
    )

    datatype EncryptOutput = EncryptOutput(
        ciphertext: seq<uint8>,
        encryptionContext: CryptographicMaterialProviders.Structures.EncryptionContext,
        algorithmSuite: string
    )

    trait IAwsEncryptionSdkClient {
        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
    }

    datatype AwsEncryptionSdkClientConfig = AwsEncryptionSdkClientConfig(
        commitmentPolicy: string,
        maxEncryptedEdks: int,
        configDefaults: string
    )

    // If we were to follow the C# example we would generate an abstract class here whose methods
    // do nothing except validate the input and then delegate out to a subclass's real
    // implementation. With Dafny the validation can be done with pre- and post-conditions.
    // But ideally we would still auto-generate the constructor/builder boilerplate.
    class AwsEncryptionSdkClient extends IAwsEncryptionSdkClient {
        const clientConfig: AwsEncryptionSdkClientConfig

        constructor(clientConfig: AwsEncryptionSdkClientConfig) {
            this.clientConfig := clientConfig;
        }

        method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>) {
            // TODO
        }
    }
}