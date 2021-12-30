namespace aws.crypto

///////////////////////////////////
// Algorithm Suites

// For now, the actual properties of algorithm suites are only used by internal
// components and are not actually customer facing. If and when we make them
// customer facing, we will need to either model the AlgorithmSuiteProperties
// as a separate structure (with an associated resource/operation for translating
// from name to properties) or use more advanced custom traits which allow us to
// model all properties of the algorithm suite in one structure. 
@enum([
    {
        name: "ALG_AES_128_GCM_IV12_TAG16_NO_KDF",
        value: "0x0014",
    },
    {
        name: "ALG_AES_192_GCM_IV12_TAG16_NO_KDF",
        value: "0x0046",
    },
    {
        name: "ALG_AES_256_GCM_IV12_TAG16_NO_KDF",
        value: "0x0078",
    },
    {
        name: "ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256",
        value: "0x0114",
    },
    {
        name: "ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256",
        value: "0x0146",
    },
    {
        name: "ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256",
        value: "0x0178",
    },
    {
        name: "ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256",
        value: "0x0214",
    },
    {
        name: "ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384",
        value: "0x0346",
    },
    {
        name: "ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384",
        value: "0x0378",
    },
    // TODO add commitment suites back in
    // {
    //     name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY",
    //     value: "0x0478",
    // },
    // {
    //     name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384",
    //     value: "0x0578",
    // },
])
string AlgorithmSuiteId


//////////
// Padding

// Values come from: https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/framework/raw-rsa-keyring.md#supported-padding-schemes
@enum([
    {
        name: "PKCS1",
        value: "PKCS1",
    },
    {
        name: "OAEP_SHA1_MGF1",
        value: "OAEP_SHA1_MGF1",
    },
    {
        name: "OAEP_SHA256_MGF1",
        value: "OAEP_SHA256_MGF1",
    },
    {
        name: "OAEP_SHA384_MGF1",
        value: "OAEP_SHA384_MGF1",
    },
    {
        name: "OAEP_SHA512_MGF1",
        value: "OAEP_SHA512_MGF1",
    },
])
string PaddingScheme


/////////////
// Commitment

@enum([
    {
        name: "FORBID_ENCRYPT_ALLOW_DECRYPT",
        value: "FORBID_ENCRYPT_ALLOW_DECRYPT",
    },
    {
        name: "REQUIRE_ENCRYPT_ALLOW_DECRYPT",
        value: "REQUIRE_ENCRYPT_ALLOW_DECRYPT",
    },
    {
        name: "REQUIRE_ENCRYPT_REQUIRE_DECRYPT",
        value: "REQUIRE_ENCRYPT_REQUIRE_DECRYPT",
    },
])
string CommitmentPolicy

//////////////////////////
// AES wrapping algorithms
@enum([
    {
        name: "ALG_AES128_GCM_IV12_TAG16",
        value: "ALG_AES128_GCM_IV12_TAG16",
    },
    {
        name: "ALG_AES192_GCM_IV12_TAG16",
        value: "ALG_AES192_GCM_IV12_TAG16",
    },
    {
        name: "ALG_AES256_GCM_IV12_TAG16",
        value: "ALG_AES256_GCM_IV12_TAG16",
    },
])
string AesWrappingAlg
