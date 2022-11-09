namespace aws.cryptography.materialProviders

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
string ESDKCommitmentPolicy

union CommitmentPolicy {
  ESDK: ESDKCommitmentPolicy
}

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
